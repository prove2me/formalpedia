-- Prove2me | solution 1 for GeneralizedUniformServer.UnitWeights.Supplement.weighted_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-20T22:25:44.458464+00:00
-- url     : https://prove2.me/submissions/e3ec7f10-f1e2-475b-b4d5-1f8ab5534735

import Mathlib
import Definitions.Def_GeneralizedUniformServer_UnitWeights_Supplement_Weighted

section
open scoped NNReal
noncomputable section
namespace GeneralizedUniformServer.Dev.WB
open GeneralizedUniformServer.UnitWeights GeneralizedUniformServer.UnitWeights.Supplement
variable {k : ℕ} {M : Fin k → Type*}
/-!
# Blueprint for `GeneralizedUniformServer.UnitWeights.Supplement.weighted_bound` (Theorem 1.3)

Paper: §5 of "Tight Bounds for Randomized Generalized k-Server on Uniform Metrics".
Lean indexing: servers are `Fin k`, 0-based. The paper's level `ℓ ∈ [1, k]` is our level index
`i = ℓ - 1`, and "server ℓ" is `srv i`. The paper's `d_ℓ` is `D i`, `m_ℓ` is `m i`
(`v (i+1) = m i * v i`).

Strategies are *fractional*: a step of a strategy is a coupling, a finitely supported
nonnegative measure on pairs of configurations (`Cpl`). `round` turns a fractional online
strategy into a `GenOnlineAlg` whose expected cost is the sum of the coupling costs.
-/
/-! ## Couplings and fractional strategies -/
/-- A coupling: a finitely supported nonnegative measure on pairs of configurations. -/
abbrev Cpl (M : Fin k → Type*) := (Config M × Config M) →₀ ℝ≥0

/-- First marginal. -/
def Cpl.fst (γ : Cpl M) : Config M →₀ ℝ≥0 := γ.mapDomain Prod.fst

/-- Second marginal. -/
def Cpl.snd (γ : Cpl M) : Config M →₀ ℝ≥0 := γ.mapDomain Prod.snd

/-- Expected weighted movement of a coupling. -/
def Cpl.cost (v : Fin k → ℝ≥0) (γ : Cpl M) : ℝ≥0 :=
  γ.sum fun xy c => c * wdist v xy.1 xy.2

/-- Total mass of a finitely supported measure. -/
def mass {α : Type*} (μ : α →₀ ℝ≥0) : ℝ≥0 := μ.sum fun _ c => c

/-- The product coupling of two finitely supported measures. -/
def prodC (μ ν : Config M →₀ ℝ≥0) : Cpl M :=
  μ.sum fun x a => ν.sum fun y b => Finsupp.single (x, y) (a * b)

/-- A fractional online strategy started at `a`: for every request prefix `h ++ [r]`, a coupling
`G (h ++ [r])` of the configuration law before `r` with the configuration law after `r`. -/
structure FracStrat (a : Config M) where
  G : List (Config M) → Cpl M
  mass_eq : ∀ h r, mass (G (h ++ [r])) = 1
  first : ∀ r, (G [r]).fst = Finsupp.single a 1
  chain : ∀ h r, h ≠ [] → (G (h ++ [r])).fst = (G h).snd
  serves : ∀ h r xy, xy ∈ (G (h ++ [r])).support → Serves xy.2 r

end GeneralizedUniformServer.Dev.WB
end
end

section
set_option autoImplicit false
open scoped NNReal
noncomputable section
namespace GeneralizedUniformServer.Dev.WB.PartR
open GeneralizedUniformServer.UnitWeights GeneralizedUniformServer.UnitWeights.Supplement
open GeneralizedUniformServer.Dev.WB
variable {k : ℕ} {M : Fin k → Type*}
/-!
# Part R: rounding a fractional strategy to a randomized online algorithm.

The algorithm draws its next configuration from the conditional law of the coupling given its
current configuration. By induction, the law of its current configuration before request `t`
is the second marginal of the coupling of step `t - 1` (the start `a` for `t = 0`), which is
the first marginal of the coupling of step `t`; hence its expected step cost is the cost of
that coupling.
-/
/-! ## Expectations under a PMF -/
/-- Expectation of `g` under a PMF, in `ℝ≥0∞`. -/
def E {α : Type*} (μ : PMF α) (g : α → ENNReal) : ENNReal := ∑' p, μ p * g p

lemma E_bind {α β : Type*} (μ : PMF α) (f : α → PMF β) (g : β → ENNReal) :
    E (μ.bind f) g = E μ (fun a => E (f a) g) := by
  unfold E
  simp_rw [PMF.bind_apply, ← ENNReal.tsum_mul_right]
  rw [ENNReal.tsum_comm]
  congr 1
  ext a
  simp_rw [← ENNReal.tsum_mul_left, mul_assoc]

lemma E_pure {α : Type*} (b : α) (g : α → ENNReal) : E (PMF.pure b) g = g b := by
  simp [E, PMF.pure_apply]

lemma E_map {α β : Type*} (h : α → β) (μ : PMF α) (g : β → ENNReal) :
    E (μ.map h) g = E μ (fun a => g (h a)) := by
  have : μ.map h = μ.bind (PMF.pure ∘ h) := rfl
  rw [this, E_bind]
  simp [E_pure]

lemma E_mono {α : Type*} (μ : PMF α) {f g : α → ENNReal} (h : ∀ a, f a ≤ g a) :
    E μ f ≤ E μ g :=
  ENNReal.tsum_le_tsum fun a => by gcongr; exact h a

lemma E_add {α : Type*} (μ : PMF α) (f g : α → ENNReal) :
    E μ (fun a => f a + g a) = E μ f + E μ g := by
  simp [E, mul_add, ENNReal.tsum_add]

lemma E_const {α : Type*} (μ : PMF α) (c : ENNReal) : E μ (fun _ => c) = c := by
  unfold E
  rw [ENNReal.tsum_mul_right, μ.tsum_coe, one_mul]

lemma traj_succ_E (A : GenOnlineAlg M (Config M)) (a : Config M) (ρ : List (Config M)) (t : ℕ)
    (ht : t < ρ.length) (g : List (Config M) → ENNReal) :
    E (genTrajLaw A a ρ (t + 1)) g =
      E (genTrajLaw A a ρ t) (fun p => E (A (ρ.take t) p ρ[t]) (fun y => g (y :: p))) := by
  rw [genTrajLaw, E_bind]
  congr 1
  ext p
  rw [dif_pos ht, E_map]

/-! ## Marginals as sums -/
open Classical in
lemma mapDomain_coe {α β : Type*} (f : α → β) (ν : α →₀ ℝ≥0) (b : β) :
    ((ν.mapDomain f b : ℝ≥0) : ENNReal) = ∑' x, if f x = b then (ν x : ENNReal) else 0 := by
  classical
  rw [tsum_eq_sum (s := ν.support)]
  · rw [Finsupp.mapDomain, Finsupp.sum_apply]
    unfold Finsupp.sum
    rw [ENNReal.ofNNReal_finsetSum]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp only [Finsupp.single_apply]
    split_ifs <;> simp
  · intro x hx
    rw [Finsupp.notMem_support_iff.mp hx]
    simp

lemma fst_coe (γ : Cpl M) (x : Config M) :
    ((γ.fst x : ℝ≥0) : ENNReal) = ∑' y, (γ (x, y) : ENNReal) := by
  rw [Cpl.fst, mapDomain_coe, ENNReal.tsum_prod']
  simp only
  rw [tsum_eq_single x]
  · simp
  · intro x' hx'
    simp [hx']

lemma snd_coe (γ : Cpl M) (y : Config M) :
    ((γ.snd y : ℝ≥0) : ENNReal) = ∑' x, (γ (x, y) : ENNReal) := by
  rw [Cpl.snd, mapDomain_coe, ENNReal.tsum_prod']
  refine tsum_congr fun x => ?_
  simp only
  rw [tsum_eq_single y]
  · simp
  · intro y' hy'
    simp [hy']

lemma cost_coe (v : Fin k → ℝ≥0) (γ : Cpl M) :
    ((γ.cost v : ℝ≥0) : ENNReal) =
      ∑' x, ∑' y, (γ (x, y) : ENNReal) * (wdist v x y : ENNReal) := by
  rw [← ENNReal.tsum_prod' (f := fun p : Config M × Config M =>
    (γ p : ENNReal) * (wdist v p.1 p.2 : ENNReal)), tsum_eq_sum (s := γ.support)]
  · unfold Cpl.cost Finsupp.sum
    push_cast
    rfl
  · intro p hp
    simp [Finsupp.notMem_support_iff.mp hp]

/-! ## The conditional kernel -/
lemma tsum_ne_zero (γ : Cpl M) (x : Config M) (h : γ.fst x ≠ 0) :
    ∑' y, (γ (x, y) : ENNReal) ≠ 0 := by
  rw [← fst_coe]
  exact_mod_cast h

lemma tsum_ne_top (γ : Cpl M) (x : Config M) : ∑' y, (γ (x, y) : ENNReal) ≠ ⊤ := by
  rw [← fst_coe]
  exact ENNReal.coe_ne_top

/-- The law of the second coordinate under `γ` given first coordinate `x` (or `pure r` if `x`
has no mass). -/
def K (γ : Cpl M) (x r : Config M) : PMF (Config M) :=
  if h : γ.fst x ≠ 0 then
    PMF.normalize (fun y => (γ (x, y) : ENNReal)) (tsum_ne_zero γ x h) (tsum_ne_top γ x)
  else PMF.pure r

lemma K_E (γ : Cpl M) (x r : Config M) (g : Config M → ENNReal) :
    (γ.fst x : ENNReal) * E (K γ x r) g = ∑' y, (γ (x, y) : ENNReal) * g y := by
  unfold K
  split_ifs with h
  · unfold E
    simp_rw [PMF.normalize_apply, ← fst_coe]
    rw [← ENNReal.tsum_mul_left]
    refine tsum_congr fun y => ?_
    have h0 : (γ.fst x : ENNReal) ≠ 0 := by exact_mod_cast h
    calc (γ.fst x : ENNReal) * ((γ (x, y) : ENNReal) * (γ.fst x : ENNReal)⁻¹ * g y)
        = ((γ.fst x : ENNReal) * (γ.fst x : ENNReal)⁻¹) * ((γ (x, y) : ENNReal) * g y) := by
          ring
      _ = (γ (x, y) : ENNReal) * g y := by
          rw [ENNReal.mul_inv_cancel h0 ENNReal.coe_ne_top, one_mul]
  · push Not at h
    have hz : ∀ y, (γ (x, y) : ENNReal) = 0 :=
      ENNReal.tsum_eq_zero.mp (by rw [← fst_coe, h]; simp)
    simp [h, hz]

lemma K_support (γ : Cpl M) (x r y : Config M) (hy : y ∈ (K γ x r).support) :
    (x, y) ∈ γ.support ∨ y = r := by
  unfold K at hy
  split_ifs at hy with h
  · left
    rw [PMF.mem_support_iff, PMF.normalize_apply] at hy
    rw [Finsupp.mem_support_iff]
    intro h'
    apply hy
    simp [h']
  · right
    simpa using hy

end GeneralizedUniformServer.Dev.WB.PartR
end
end

section
set_option autoImplicit false
open scoped NNReal
noncomputable section
namespace GeneralizedUniformServer.Dev.WB.PartR
open GeneralizedUniformServer.UnitWeights GeneralizedUniformServer.UnitWeights.Supplement
open GeneralizedUniformServer.Dev.WB
variable {k : ℕ} {M : Fin k → Type*}
variable (a : Config M) (F : FracStrat a)
/-! ## The algorithm -/
/-- The rounded algorithm. -/
def alg : GenOnlineAlg M (Config M) := fun hist path r =>
  K (F.G (hist ++ [r])) (path.headD a) r

/-- The configuration law before request `t`. -/
def prev (ρ : List (Config M)) (t : ℕ) : Config M →₀ ℝ≥0 :=
  if t = 0 then Finsupp.single a 1 else (F.G (ρ.take t)).snd

lemma take_succ' (ρ : List (Config M)) (s : ℕ) (hs : s < ρ.length) :
    ρ.take (s + 1) = ρ.take s ++ [ρ[s]] := by
  rw [List.take_add_one, List.getElem?_eq_getElem hs]
  rfl

lemma fst_eq_prev (ρ : List (Config M)) (t : ℕ) (ht : t < ρ.length) :
    (F.G (ρ.take t ++ [ρ[t]])).fst = prev a F ρ t := by
  unfold prev
  split_ifs with h
  · subst h
    simpa using F.first ρ[0]
  · refine F.chain _ _ ?_
    intro h'
    have := congrArg List.length h'
    simp only [List.length_take, List.length_nil] at this
    omega

lemma head_law (ρ : List (Config M)) (t : ℕ) (ht : t ≤ ρ.length) (h : Config M → ENNReal) :
    E (genTrajLaw (alg a F) a ρ t) (fun p => h (p.headD a)) =
      ∑' x, (prev a F ρ t x : ENNReal) * h x := by
  induction t generalizing h with
  | zero =>
    simp only [genTrajLaw, E_pure, List.headD_cons, prev, if_true]
    rw [tsum_eq_single a]
    · rw [Finsupp.single_eq_same]
      simp
    · intro x hx
      simp [Ne.symm hx]
  | succ t ih =>
    have ht' : t < ρ.length := ht
    rw [traj_succ_E _ _ _ _ ht']
    simp only [List.headD_cons]
    have e := ih ht'.le (fun x => E (K (F.G (ρ.take t ++ [ρ[t]])) x ρ[t]) h)
    have e2 : (fun p : List (Config M) => E (alg a F (ρ.take t) p ρ[t]) h) =
        fun p => E (K (F.G (ρ.take t ++ [ρ[t]])) (p.headD a) ρ[t]) h := rfl
    rw [e2, e, ← fst_eq_prev a F ρ t ht']
    simp_rw [K_E]
    rw [ENNReal.tsum_comm]
    have hp : prev a F ρ (t + 1) = (F.G (ρ.take t ++ [ρ[t]])).snd := by
      unfold prev
      rw [if_neg (Nat.succ_ne_zero t), take_succ' ρ t ht']
    rw [hp]
    simp_rw [snd_coe, ENNReal.tsum_mul_right]

lemma wPathCost_cons_le (v : Fin k → ℝ≥0) (y : Config M) (p : List (Config M)) :
    ((wPathCost v (y :: p) : ℝ≥0) : ENNReal) ≤
      (wdist v (p.headD a) y : ENNReal) + (wPathCost v p : ENNReal) := by
  cases p with
  | nil => simp [wPathCost]
  | cons x q => simp [wPathCost]

lemma step_cost (v : Fin k → ℝ≥0) (ρ : List (Config M)) (s : ℕ) (hs : s < ρ.length) :
    E (genTrajLaw (alg a F) a ρ s) (fun p =>
        E (K (F.G (ρ.take s ++ [ρ[s]])) (p.headD a) ρ[s])
          (fun y => (wdist v (p.headD a) y : ENNReal))) =
      (((F.G (ρ.take (s + 1))).cost v : ℝ≥0) : ENNReal) := by
  rw [head_law a F ρ s hs.le (fun x => E (K (F.G (ρ.take s ++ [ρ[s]])) x ρ[s])
    (fun y => (wdist v x y : ENNReal))), ← fst_eq_prev a F ρ s hs]
  simp_rw [K_E]
  rw [cost_coe, take_succ' ρ s hs]

lemma cost_le (v : Fin k → ℝ≥0) (ρ : List (Config M)) (t : ℕ) (ht : t ≤ ρ.length) :
    E (genTrajLaw (alg a F) a ρ t) (fun p => (wPathCost v p : ENNReal)) ≤
      ∑ s ∈ Finset.range t, (((F.G (ρ.take (s + 1))).cost v : ℝ≥0) : ENNReal) := by
  induction t with
  | zero => simp [genTrajLaw, E_pure, wPathCost]
  | succ t ih =>
    have ht' : t < ρ.length := ht
    rw [traj_succ_E _ _ _ _ ht', Finset.sum_range_succ, add_comm _ (((F.G _).cost v : ℝ≥0) :
      ENNReal), ← step_cost a F v ρ t ht']
    calc E (genTrajLaw (alg a F) a ρ t) (fun p => E (alg a F (ρ.take t) p ρ[t])
          (fun y => (wPathCost v (y :: p) : ENNReal)))
        ≤ E (genTrajLaw (alg a F) a ρ t) (fun p =>
            E (K (F.G (ρ.take t ++ [ρ[t]])) (p.headD a) ρ[t])
              (fun y => (wdist v (p.headD a) y : ENNReal)) + (wPathCost v p : ENNReal)) := by
          refine E_mono _ fun p => ?_
          rw [← E_const (K (F.G (ρ.take t ++ [ρ[t]])) (p.headD a) ρ[t])
            (wPathCost v p : ENNReal), ← E_add]
          exact E_mono _ fun y => wPathCost_cons_le a v y p
      _ ≤ _ := by
          rw [E_add]
          exact add_le_add le_rfl (ih ht'.le)

theorem round [NeZero k] (v : Fin k → ℝ≥0) (a : Config M) (F : FracStrat a) :
    ∃ A : GenOnlineAlg M (Config M), IsServing Serves A ∧
      ∀ ρ : List (Config M),
        genExpectedCostW v A a ρ ≤
          ∑ s ∈ Finset.range ρ.length, (((F.G (ρ.take (s + 1))).cost v : ℝ≥0) : ENNReal) := by
  refine ⟨alg a F, ?_, fun ρ => cost_le a F v ρ ρ.length le_rfl⟩
  intro hist path r y hy
  rcases K_support _ _ _ _ hy with h | h
  · exact F.serves hist r _ h
  · subst h
    exact ⟨⟨0, NeZero.pos k⟩, rfl⟩

end GeneralizedUniformServer.Dev.WB.PartR
end
end

section
open scoped NNReal
noncomputable section
namespace GeneralizedUniformServer.Dev.WB
open GeneralizedUniformServer.UnitWeights GeneralizedUniformServer.UnitWeights.Supplement
variable {k : ℕ} {M : Fin k → Type*}
alias round := GeneralizedUniformServer.Dev.WB.PartR.round

/-! ## Chains -/
/-- `l` is a chain of couplings started from the law `μ`: consecutive marginals match. -/
def IsChainD : (Config M →₀ ℝ≥0) → List (Cpl M) → Prop
  | _, [] => True
  | μ, γ :: l => γ.fst = μ ∧ IsChainD γ.snd l

/-- Total cost of a list of couplings. -/
def chainCost (v : Fin k → ℝ≥0) (l : List (Cpl M)) : ℝ≥0 := (l.map (Cpl.cost v)).sum

end GeneralizedUniformServer.Dev.WB
end
end

section
open scoped NNReal
noncomputable section
namespace GeneralizedUniformServer.Dev.WB
open GeneralizedUniformServer.UnitWeights GeneralizedUniformServer.UnitWeights.Supplement
variable {k : ℕ} {M : Fin k → Type*}
variable (v : Fin k → ℝ≥0) (Δ : ℝ≥0) {ι : Type*}
/-! ## The master of Lemma 5.3 (fractional, "shrinking dartboard" form) -/
/-- Cost of the first `t + 1` steps of a chain. -/
def cumCost (l : List (Cpl M)) (t : ℕ) : ℝ≥0 :=
  ∑ s ∈ Finset.range (t + 1), (l.getD s 0).cost v

/-- Weight `ω_p(t)` of an expert whose chain is `l`: `exp(-cumCost/Δ)` while active
(`t < l.length`), else `0`. -/
def mWeight (l : List (Cpl M)) (t : ℕ) : ℝ≥0 :=
  if t < l.length then Real.toNNReal (Real.exp (-(cumCost v l t : ℝ) / (Δ : ℝ))) else 0

/-- Normalized weights `ν_t(p)`. -/
def mNu (S : Finset ι) (cp : ι → List (Cpl M)) (t : ℕ) (p : ι) : ℝ≥0 :=
  mWeight v Δ (cp p) t / ∑ q ∈ S, mWeight v Δ (cp q) t

/-- The master's configuration law after step `t`: `∑_p ν_t(p) μ^p_t`. -/
def mDist (S : Finset ι) (cp : ι → List (Cpl M)) (t : ℕ) : Config M →₀ ℝ≥0 :=
  ∑ p ∈ S, mNu v Δ S cp t p • ((cp p).getD t 0).snd

/-- Mass kept on expert `p` at step `t ≥ 1`: `ν_{t-1}(p) e^{-λ_p(t)/Δ} 1[p active at t]`. -/
def mKeep (S : Finset ι) (cp : ι → List (Cpl M)) (t : ℕ) (p : ι) : ℝ≥0 :=
  if t < (cp p).length then
    mNu v Δ S cp (t - 1) p *
      Real.toNNReal (Real.exp (-(((cp p).getD t 0).cost v : ℝ) / (Δ : ℝ)))
  else 0

/-- The master chain started at `y`, over `n` steps, following experts `S` with chains `cp`.
Step `0` moves from `y` straight to the law `mDist 0`; at step `t ≥ 1` the master stays with
its expert `p` with probability `mKeep t p / ν_{t-1}(p)` (following that expert's own
coupling), and otherwise resamples from `mDist t`. -/
def master (y : Config M) (S : Finset ι) (cp : ι → List (Cpl M)) (n : ℕ) : List (Cpl M) :=
  List.ofFn fun t : Fin n =>
    if t.val = 0 then prodC (Finsupp.single y 1) (mDist v Δ S cp 0)
    else
      (∑ p ∈ S, mKeep v Δ S cp t p • (cp p).getD t 0) +
        prodC (∑ p ∈ S, (mNu v Δ S cp (t - 1) p - mKeep v Δ S cp t p) •
            ((cp p).getD (t - 1) 0).snd)
          (mDist v Δ S cp t)

/-- Hypotheses on the experts of the master. `B` is a set of diameter `≤ Δ` containing `y`
and every configuration the experts use; every expert `p ∈ S` has a chain from its own
start `st p ∈ B`, of length `≤ n`, and some expert lasts all `n` steps (or `n = 0`). -/
structure MasterHyp (y : Config M) (S : Finset ι) (cp : ι → List (Cpl M)) (n : ℕ)
    (st : ι → Config M) (B : Set (Config M)) : Prop where
  pos : 0 < Δ
  diam : ∀ z ∈ B, ∀ z' ∈ B, wdist v z z' ≤ Δ
  hy : y ∈ B
  nonempty : S.Nonempty
  chain : ∀ p ∈ S, IsChainD (Finsupp.single (st p) 1) (cp p)
  st_mem : ∀ p ∈ S, st p ∈ B
  supp : ∀ p ∈ S, ∀ γ ∈ cp p, ∀ xy ∈ γ.support, xy.2 ∈ B
  len_le : ∀ p ∈ S, (cp p).length ≤ n
  len_eq : n = 0 ∨ ∃ p ∈ S, (cp p).length = n

end GeneralizedUniformServer.Dev.WB
end
end

section
set_option autoImplicit false
open scoped NNReal
noncomputable section
namespace GeneralizedUniformServer.Dev.WB.PartM
open GeneralizedUniformServer.UnitWeights GeneralizedUniformServer.UnitWeights.Supplement
open GeneralizedUniformServer.Dev.WB
/-!
# Part M: the master of Lemma 5.3 (`master_chain`, `master_supp`, `master_cost`, `master_take`).
-/
/-! ## The real inequality of one step -/
lemma real_step {ι : Type*} (S : Finset ι) (a b lam : ι → ℝ) (Δ : ℝ) (hΔ : 0 < Δ)
    (hb : ∀ p ∈ S, 0 ≤ b p) (hl : ∀ p ∈ S, 0 ≤ lam p)
    (hab : ∀ p ∈ S, b p * Real.exp (lam p / Δ) ≤ a p)
    (hA : 0 < ∑ p ∈ S, a p) (hB : 0 < ∑ p ∈ S, b p) :
    ∑ p ∈ S, b p / (∑ q ∈ S, a q) * lam p + Δ * (1 - (∑ q ∈ S, b q) / (∑ q ∈ S, a q)) ≤
      2 * Δ * (Real.log (∑ q ∈ S, a q) - Real.log (∑ q ∈ S, b q)) := by
  set A := ∑ q ∈ S, a q with hAdef
  set Bs := ∑ q ∈ S, b q with hBdef
  set ψ := Real.log A - Real.log Bs with hψ
  have h1 : 1 - Bs / A ≤ ψ := by
    have := Real.log_le_sub_one_of_pos (div_pos hB hA)
    rw [Real.log_div hB.ne' hA.ne'] at this
    linarith
  have hba : ∀ p ∈ S, b p ≤ a p := fun p hp =>
    le_trans (le_mul_of_one_le_right (hb p hp)
      (Real.one_le_exp (div_nonneg (hl p hp) hΔ.le))) (hab p hp)
  have hBA : Bs ≤ A := Finset.sum_le_sum hba
  have h2 : ∑ p ∈ S, b p / A * lam p ≤ ∑ p ∈ S, b p / Bs * lam p := by
    refine Finset.sum_le_sum fun p hp => ?_
    exact mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_left (hb p hp) hB hBA) (hl p hp)
  have key : ∀ p ∈ S, b p / Bs * lam p ≤ Δ * (a p / A - b p / Bs) + Δ * ψ * (b p / Bs) := by
    intro p hp
    set u := b p / Bs with hu
    have hu0 : 0 ≤ u := div_nonneg (hb p hp) hB.le
    have e1 : u * (lam p / Δ - ψ) + u ≤ u * Real.exp (lam p / Δ - ψ) := by
      have := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (lam p / Δ - ψ)) hu0
      linarith
    have e2 : u * Real.exp (lam p / Δ - ψ) = b p * Real.exp (lam p / Δ) / A := by
      rw [Real.exp_sub, hψ, Real.exp_sub, Real.exp_log hA, Real.exp_log hB, hu]
      field_simp
    have e3 : b p * Real.exp (lam p / Δ) / A ≤ a p / A :=
      div_le_div_of_nonneg_right (hab p hp) hA.le
    have e4 := mul_le_mul_of_nonneg_left (e1.trans (e2 ▸ e3)) hΔ.le
    have hx : Δ * (u * (lam p / Δ - ψ) + u) = u * lam p - Δ * ψ * u + Δ * u := by
      field_simp
    rw [hx] at e4
    linarith
  have hsa : ∑ p ∈ S, a p / A = 1 := by rw [← Finset.sum_div, div_self hA.ne']
  have hsb : ∑ p ∈ S, b p / Bs = 1 := by rw [← Finset.sum_div, div_self hB.ne']
  have h3 := Finset.sum_le_sum key
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_sub_distrib, hsa,
    hsb] at h3
  have h1' := mul_le_mul_of_nonneg_left h1 hΔ.le
  linarith

end GeneralizedUniformServer.Dev.WB.PartM
end
end

section
open scoped NNReal
noncomputable section
namespace GeneralizedUniformServer.Dev.WB
open GeneralizedUniformServer.UnitWeights GeneralizedUniformServer.UnitWeights.Supplement
variable {k : ℕ} {M : Fin k → Type*}
/-! ## Phases (Definition 5.1) -/
/-- Server `i` (mod `k`); for `i < k` this is `⟨i, _⟩`. -/
def srv [NeZero k] (i : ℕ) : Fin k := ⟨i % k, Nat.mod_lt _ (NeZero.pos k)⟩

/-- A set `U ∈ U_ℓ`: at most one point of each `M j`. -/
abbrev PSet (M : Fin k → Type*) := (j : Fin k) → Option (M j)

/-- `U` satisfies the request `r`: `r j ∈ U` for some `j`. -/
def Sat (U : PSet M) (r : Config M) : Prop := ∃ j, U j = some (r j)

/-- `x` covers `U`. -/
def Covers (x : Config M) (U : PSet M) : Prop := ∀ j u, U j = some u → x j = u

/-- Demand vectors, one finitely supported `ℕ`-valued function per space. -/
abbrev Demand (M : Fin k → Type*) := (j : Fin k) → (M j →₀ ℕ)

/-- Result of parsing a phase or multiphase on a finite list of requests. `stop = some n`:
the part accepted the requests with indices `< n` and stopped at the request with index `n`
(so `n < ρ.length`); `stop = none`: it accepted every request of the list without stopping.
`dem` is the demand vector (meaningful only when stopped). -/
structure PR (M : Fin k → Type*) where
  stop : Option ℕ
  dem : Demand M

open Classical in
/-- Index of the first request not satisfying `P` (`none` if all satisfy it). -/
def scan (P : Config M → Prop) : List (Config M) → Option ℕ
  | [] => none
  | r :: ρ => if P r then (scan P ρ).map (· + 1) else some 0

open Classical in
/-- The `(1, U)`-phase (level index `0`). -/
def phase0 [NeZero k] (U : PSet M) : List (Config M) → PR M
  | [] => ⟨none, 0⟩
  | r :: ρ =>
    if Sat U r then ⟨(phase0 U ρ).stop.map (· + 1), (phase0 U ρ).dem⟩
    else
      match scan (Sat (Function.update U (srv 0) (some (r (srv 0))))) ρ with
      | none => ⟨none, 0⟩
      | some n => ⟨some (n + 1), fun j => Finsupp.single (r j) 1⟩

/-- Run `m` copies of the part `f` one after another (a multiphase). -/
def iter (f : List (Config M) → PR M) : ℕ → List (Config M) → PR M
  | 0, _ => ⟨some 0, 0⟩
  | m + 1, ρ =>
    match (f ρ).stop with
    | none => ⟨none, 0⟩
    | some n => ⟨(iter f m (ρ.drop n)).stop.map (n + ·), (f ρ).dem + (iter f m (ρ.drop n)).dem⟩

open Classical in
/-- The critical set: `n` points of largest demand, chosen greedily (fewer if the space has
fewer than `n` points). -/
def crit {α : Type*} (V : α →₀ ℕ) : ℕ → Finset α
  | 0 => ∅
  | n + 1 =>
    if h : ∃ q, q ∉ crit V n ∧ ∀ q', q' ∉ crit V n → V q' ≤ V q then
      insert (Classical.choose h) (crit V n)
    else crit V n

/-- `d_ℓ = 2^{5^{ℓ-1} - 1}` at level index `i = ℓ - 1`. -/
def D (i : ℕ) : ℕ := 2 ^ (5 ^ i - 1)

open Classical in
/-- The `(ℓ, U)`-phase at level index `i = ℓ - 1`, with `m i` phases per level-`i`
multiphase. -/
def phase [NeZero k] (m : ℕ → ℕ) : ℕ → PSet M → List (Config M) → PR M
  | 0, U, ρ => phase0 U ρ
  | i + 1, U, ρ =>
    match (iter (phase m i U) (m i) ρ).stop with
    | none => ⟨none, 0⟩
    | some e =>
      if ∀ p ∈ crit ((iter (phase m i U) (m i) ρ).dem (srv (i + 1))) (D (i + 1) - 1),
          (iter (phase m i (Function.update U (srv (i + 1)) (some p))) (m i) (ρ.drop e)).stop ≠ none
      then
        ⟨some (e + (crit ((iter (phase m i U) (m i) ρ).dem (srv (i + 1))) (D (i + 1) - 1)).sup
            fun p => ((iter (phase m i (Function.update U (srv (i + 1)) (some p))) (m i)
              (ρ.drop e)).stop.getD 0)),
          (iter (phase m i U) (m i) ρ).dem +
            ∑ p ∈ crit ((iter (phase m i U) (m i) ρ).dem (srv (i + 1))) (D (i + 1) - 1),
              (iter (phase m i (Function.update U (srv (i + 1)) (some p))) (m i) (ρ.drop e)).dem⟩
      else ⟨none, 0⟩

/-- Number of consecutive top-level `(k, ∅)`-phases that the parser starts on `ρ`
(`fuel` bounds the recursion; `ncalls` uses `fuel = ρ.length`). -/
def ncallsAux (f : List (Config M) → PR M) : ℕ → List (Config M) → ℕ
  | 0, _ => 0
  | _ + 1, [] => 0
  | fuel + 1, r :: ρ =>
    match (f (r :: ρ)).stop with
    | none => 1
    | some n => 1 + ncallsAux f fuel ((r :: ρ).drop n)

/-- The number `n_c` of `(k, ∅)`-phase calls on `ρ`. -/
def ncalls [NeZero k] (m : ℕ → ℕ) (ρ : List (Config M)) : ℕ :=
  ncallsAux (phase m (k - 1) (fun _ => none)) ρ.length ρ

/-- Normalized weights: positive, consecutive ratios `m i ∈ {2, 3, …}`. -/
def Normalized [NeZero k] (v : Fin k → ℝ≥0) (m : ℕ → ℕ) : Prop :=
  (∀ j, 0 < v j) ∧ ∀ i (h : i + 1 < k), 2 ≤ m i ∧ v ⟨i + 1, h⟩ = m i * v ⟨i, by omega⟩

end GeneralizedUniformServer.Dev.WB
end
end

section
set_option autoImplicit false
open scoped NNReal
noncomputable section
namespace GeneralizedUniformServer.Dev.WB.PartL
open GeneralizedUniformServer.UnitWeights GeneralizedUniformServer.UnitWeights.Supplement
open GeneralizedUniformServer.Dev.WB
variable {k : ℕ} {M : Fin k → Type*}
/-!
# Part L: the offline lower bound (paper §5.4)

Lemma 5.9, Corollary 5.10 and the sum over the top-level phase calls.
-/
/-! ## Solutions and their costs -/
/-- `ξ` is a solution for the first `n` requests of `ρ`. -/
def Sol (ρ : List (Config M)) (n : ℕ) (ξ : ℕ → Config M) : Prop :=
  ∀ t < n, ∀ r, ρ[t]? = some r → Serves (ξ (t + 1)) r

/-- Cost of `ξ` between indices `a` and `b`. -/
def cI (v : Fin k → ℝ≥0) (ξ : ℕ → Config M) (a b : ℕ) : ℝ :=
  ∑ t ∈ Finset.Ico a b, (wdist v (ξ t) (ξ (t + 1)) : ℝ)

end GeneralizedUniformServer.Dev.WB.PartL
end
end

section
set_option autoImplicit false
open scoped NNReal
noncomputable section
namespace GeneralizedUniformServer.Dev.WB.PartL
open GeneralizedUniformServer.UnitWeights GeneralizedUniformServer.UnitWeights.Supplement
open GeneralizedUniformServer.Dev.WB
variable {k : ℕ} {M : Fin k → Type*}
variable (v : Fin k → ℝ≥0) (ξ : ℕ → Config M)
theorem cI_nonneg (a b : ℕ) : 0 ≤ cI v ξ a b :=
  Finset.sum_nonneg fun _ _ => NNReal.coe_nonneg _

theorem cI_mono {a b a' b' : ℕ} (h1 : a' ≤ a) (h2 : b ≤ b') : cI v ξ a b ≤ cI v ξ a' b' :=
  Finset.sum_le_sum_of_subset_of_nonneg (Finset.Ico_subset_Ico h1 h2)
    (fun _ _ _ => NNReal.coe_nonneg _)

theorem cI_add {a b c : ℕ} (h1 : a ≤ b) (h2 : b ≤ c) : cI v ξ a b + cI v ξ b c = cI v ξ a c :=
  Finset.sum_Ico_consecutive _ h1 h2

end GeneralizedUniformServer.Dev.WB.PartL
end
end

section
set_option autoImplicit false
open scoped NNReal
noncomputable section
namespace GeneralizedUniformServer.Dev.WB.PartF
open GeneralizedUniformServer.UnitWeights GeneralizedUniformServer.UnitWeights.Supplement
open GeneralizedUniformServer.Dev.WB
variable {k : ℕ} {M : Fin k → Type*}
/-!
# Part F: the theorem (paper §5.5).

Cases: `w 0 = 0` (move server `0` to `r 0`, cost `0`); `k = 1` (move to the request, which is
what every offline solution does); otherwise round the weights to `v` with integer ratios
`≥ 2` and combine `strat_bound`, `offline_bound` and `round`.
-/
/-! ## Deterministic strategies -/
/-- The position of the deterministic strategy with transition `nx` after the requests `h`. -/
def pos (a : Config M) (nx : Config M → Config M → Config M) (h : List (Config M)) : Config M :=
  h.foldl nx a

/-- A deterministic fractional strategy: single couplings. -/
def detStrat (a : Config M) (nx : Config M → Config M → Config M)
    (hnx : ∀ x r, Serves (nx x r) r) : FracStrat a where
  G h := Finsupp.single (pos a nx h.dropLast, pos a nx h) 1
  mass_eq h r := by
    unfold mass
    exact Finsupp.sum_single_index rfl
  first r := by
    unfold Cpl.fst
    rw [Finsupp.mapDomain_single]
    simp [pos]
  chain h r _ := by
    unfold Cpl.fst Cpl.snd
    rw [Finsupp.mapDomain_single, Finsupp.mapDomain_single]
    simp
  serves h r xy hxy := by
    rw [Finsupp.support_single _ one_ne_zero, Finset.mem_singleton] at hxy
    subst hxy
    simp only [pos, List.foldl_append, List.foldl_cons, List.foldl_nil]
    exact hnx _ _

lemma take_succ' (ρ : List (Config M)) (s : ℕ) (hs : s < ρ.length) :
    ρ.take (s + 1) = ρ.take s ++ [ρ[s]] := by
  rw [List.take_add_one, List.getElem?_eq_getElem hs]
  rfl

lemma detStrat_cost (a : Config M) (nx : Config M → Config M → Config M)
    (hnx : ∀ x r, Serves (nx x r) r) (v : Fin k → ℝ≥0) (h : List (Config M)) (r : Config M) :
    ((detStrat a nx hnx).G (h ++ [r])).cost v = wdist v (pos a nx h) (nx (pos a nx h) r) := by
  show Cpl.cost v (Finsupp.single _ 1) = _
  unfold Cpl.cost
  rw [Finsupp.sum_single_index (by simp), one_mul]
  simp [pos]

/-! ## Passing to the offline optimum -/
lemma le_opt (w : Fin k → ℝ≥0) (a : Config M) (ρ : List (Config M)) (X C c : ENNReal)
    (hc0 : c ≠ 0) (hct : c ≠ ⊤)
    (h : ∀ o : Fin (ρ.length + 1) → Config M, IsOfflineSolution ρ o → o 0 = a →
      X ≤ c * ((wOfflineCost w ρ o : ℝ≥0) : ENNReal) + C) :
    X ≤ c * optCostW w a ρ + C := by
  unfold optCostW
  simp_rw [ENNReal.mul_iInf_of_ne hc0 hct, ENNReal.iInf_add]
  exact le_iInf fun o => le_iInf fun ho => le_iInf fun h0 => h o ho h0

/-! ## Case `w 0 = 0` -/
lemma wdist_update_zero [NeZero k] (w : Fin k → ℝ≥0) (hw0 : w 0 = 0) (x : Config M)
    (u : M 0) : wdist w x (Function.update x 0 u) = 0 := by
  classical
  unfold wdist
  refine Finset.sum_eq_zero fun i _ => ?_
  by_cases hi : i = 0
  · subst hi
    simp [hw0]
  · simp [Function.update_of_ne hi]

theorem case_w0 [NeZero k] (w : Fin k → ℝ≥0) (hw0 : w 0 = 0) (a : Config M) :
    ∃ A : GenOnlineAlg M (Config M),
      IsServing Serves A ∧
      ∀ ρ : List (Config M),
        genExpectedCostW w A a ρ ≤
          (20 : ENNReal) ^ k * optCostW w a ρ +
            (10 : ENNReal) ^ k *
              ((w ⟨k - 1, Nat.sub_lt (NeZero.pos k) Nat.one_pos⟩ : ℝ≥0) : ENNReal) := by
  let nx : Config M → Config M → Config M := fun x r => Function.update x 0 (r 0)
  have hnx : ∀ x r, Serves (nx x r) r := fun x r => ⟨0, by simp [nx]⟩
  obtain ⟨A, hA, hc⟩ := round w a (detStrat a nx hnx)
  refine ⟨A, hA, fun ρ => ?_⟩
  have h0 : ∑ s ∈ Finset.range ρ.length,
      ((((detStrat a nx hnx).G (ρ.take (s + 1))).cost w : ℝ≥0) : ENNReal) = 0 := by
    refine Finset.sum_eq_zero fun s hs => ?_
    rw [take_succ' ρ s (Finset.mem_range.mp hs), detStrat_cost a nx hnx w]
    simp [nx, wdist_update_zero w hw0]
  calc _ ≤ _ := hc ρ
    _ = 0 := h0
    _ ≤ _ := by positivity

/-! ## Case `k = 1` -/
theorem case_k1 [NeZero k] (hk : k = 1) (w : Fin k → ℝ≥0) (a : Config M) :
    ∃ A : GenOnlineAlg M (Config M),
      IsServing Serves A ∧
      ∀ ρ : List (Config M),
        genExpectedCostW w A a ρ ≤
          (20 : ENNReal) ^ k * optCostW w a ρ +
            (10 : ENNReal) ^ k *
              ((w ⟨k - 1, Nat.sub_lt (NeZero.pos k) Nat.one_pos⟩ : ℝ≥0) : ENNReal) := by
  let nx : Config M → Config M → Config M := fun _ r => r
  have hnx : ∀ x r, Serves (nx x r) r := fun x r => ⟨⟨0, NeZero.pos k⟩, rfl⟩
  obtain ⟨A, hA, hc⟩ := round w a (detStrat a nx hnx)
  refine ⟨A, hA, fun ρ => ?_⟩
  have hc20 : (20 : ENNReal) ^ k ≠ 0 := by simp
  have hct : (20 : ENNReal) ^ k ≠ ⊤ := by simp
  refine le_opt w a ρ _ _ _ hc20 hct fun o ho h0 => ?_
  refine (hc ρ).trans ?_
  -- every offline solution is the strategy's own trajectory
  have hpos : ∀ j : Fin (ρ.length + 1), o j = pos a nx (ρ.take j) := by
    intro j
    obtain ⟨j, hj⟩ := j
    cases j with
    | zero => simpa [pos] using h0
    | succ s =>
      have hs : s < ρ.length := by omega
      obtain ⟨i, hi⟩ := ho ⟨s, hs⟩
      have hsucc : (⟨s, hs⟩ : Fin ρ.length).succ = ⟨s + 1, hj⟩ := rfl
      rw [hsucc] at hi
      show o ⟨s + 1, hj⟩ = pos a nx (ρ.take (s + 1))
      rw [take_succ' ρ s hs]
      simp only [pos, List.foldl_append, List.foldl_cons, List.foldl_nil, nx]
      funext i'
      have : i' = i := Fin.ext (by have := i.2; have := i'.2; omega)
      subst this
      exact hi
  have hcost : ∑ s ∈ Finset.range ρ.length,
      ((((detStrat a nx hnx).G (ρ.take (s + 1))).cost w : ℝ≥0) : ENNReal) =
      ((wOfflineCost w ρ o : ℝ≥0) : ENNReal) := by
    unfold wOfflineCost
    rw [ENNReal.ofNNReal_finsetSum]
    have e1 : ∑ s : Fin ρ.length, ((wdist w (o s.castSucc) (o s.succ) : ℝ≥0) : ENNReal) =
        ∑ s : Fin ρ.length,
          ((wdist w (pos a nx (ρ.take s)) (pos a nx (ρ.take (s + 1))) : ℝ≥0) : ENNReal) := by
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [hpos, hpos]
      rfl
    rw [e1, Fin.sum_univ_eq_sum_range
      (fun s => ((wdist w (pos a nx (ρ.take s)) (pos a nx (ρ.take (s + 1))) : ℝ≥0) : ENNReal))]
    refine Finset.sum_congr rfl fun s hs => ?_
    have hs' := Finset.mem_range.mp hs
    rw [take_succ' ρ s hs', detStrat_cost a nx hnx w]
    simp only [pos, nx, List.foldl_append, List.foldl_cons, List.foldl_nil]
  rw [hcost]
  refine le_add_right (le_mul_of_one_le_left' ?_)
  exact one_le_pow₀ (by norm_num)

/-! ## Rounding the weights -/
/-- The weights as a function on `ℕ` (`0` beyond `k`). -/
def wN (w : Fin k → ℝ≥0) (i : ℕ) : ℝ≥0 := if h : i < k then w ⟨i, h⟩ else 0

lemma wN_val (w : Fin k → ℝ≥0) (j : Fin k) : wN w j = w j := by
  simp [wN, j.2]

/-- The rounded weights: `v 0 = W 0`, `v (i+1) = max 2 ⌈W (i+1) / v i⌉ * v i`. -/
def vv (W : ℕ → ℝ≥0) : ℕ → ℝ≥0
  | 0 => W 0
  | i + 1 => ((max 2 ⌈W (i + 1) / vv W i⌉₊ : ℕ) : ℝ≥0) * vv W i

/-- The ratios. -/
def mm (W : ℕ → ℝ≥0) (i : ℕ) : ℕ := max 2 ⌈W (i + 1) / vv W i⌉₊

lemma vv_succ (W : ℕ → ℝ≥0) (i : ℕ) : vv W (i + 1) = (mm W i : ℝ≥0) * vv W i := rfl

lemma vv_pos (W : ℕ → ℝ≥0) (h0 : 0 < W 0) : ∀ i, 0 < vv W i
  | 0 => h0
  | i + 1 => by
    rw [vv_succ]
    have := vv_pos W h0 i
    have h2 : (0 : ℝ≥0) < (mm W i : ℝ≥0) := by
      have : 2 ≤ mm W i := le_max_left _ _
      exact_mod_cast (by omega : 0 < mm W i)
    positivity

lemma le_vv (W : ℕ → ℝ≥0) (h0 : 0 < W 0) : ∀ i, W i ≤ vv W i
  | 0 => le_rfl
  | i + 1 => by
    rw [vv_succ, mm]
    have hp := vv_pos W h0 i
    calc W (i + 1) = W (i + 1) / vv W i * vv W i := by rw [div_mul_cancel₀ _ hp.ne']
      _ ≤ (⌈W (i + 1) / vv W i⌉₊ : ℝ≥0) * vv W i := by gcongr; exact Nat.le_ceil _
      _ ≤ _ := by gcongr; exact_mod_cast le_max_right _ _

lemma vv_le (W : ℕ → ℝ≥0) (h0 : 0 < W 0) (hmono : ∀ i, i + 1 < k → W i ≤ W (i + 1)) :
    ∀ i, i < k → vv W i ≤ 2 ^ i * W i
  | 0, _ => by simp [vv]
  | i + 1, hi => by
    have ih := vv_le W h0 hmono i (by omega)
    have hm := hmono i hi
    have hp := vv_pos W h0 i
    have h1 : (1 : ℝ≥0) ≤ 2 ^ i := one_le_pow₀ (by norm_num)
    have ih' : vv W i ≤ 2 ^ i * W (i + 1) := ih.trans (by gcongr)
    rw [vv_succ, mm, Nat.cast_max]
    rcases le_total ((⌈W (i + 1) / vv W i⌉₊ : ℕ) : ℝ≥0) ((2 : ℕ) : ℝ≥0) with hc | hc
    · rw [max_eq_left hc]
      calc ((2 : ℕ) : ℝ≥0) * vv W i ≤ 2 * (2 ^ i * W (i + 1)) := by
            rw [Nat.cast_ofNat]; gcongr
        _ = 2 ^ (i + 1) * W (i + 1) := by ring
    · rw [max_eq_right hc]
      have hlt : ((⌈W (i + 1) / vv W i⌉₊ : ℕ) : ℝ≥0) < W (i + 1) / vv W i + 1 :=
        Nat.ceil_lt_add_one (by positivity)
      calc ((⌈W (i + 1) / vv W i⌉₊ : ℕ) : ℝ≥0) * vv W i
          ≤ (W (i + 1) / vv W i + 1) * vv W i := by gcongr
        _ = W (i + 1) + vv W i := by rw [add_mul, div_mul_cancel₀ _ hp.ne', one_mul]
        _ ≤ 2 ^ i * W (i + 1) + 2 ^ i * W (i + 1) := by
            gcongr
            calc W (i + 1) = 1 * W (i + 1) := (one_mul _).symm
              _ ≤ 2 ^ i * W (i + 1) := by gcongr
        _ = 2 ^ (i + 1) * W (i + 1) := by ring

/-! ## Weight comparisons -/
lemma wdist_mono (w v : Fin k → ℝ≥0) (h : ∀ j, w j ≤ v j) (x y : Config M) :
    wdist w x y ≤ wdist v x y := by
  unfold wdist
  refine Finset.sum_le_sum fun i _ => ?_
  split_ifs
  · exact h i
  · exact le_rfl

lemma wdist_scale (w v : Fin k → ℝ≥0) (c : ℝ≥0) (h : ∀ j, v j ≤ c * w j) (x y : Config M) :
    wdist v x y ≤ c * wdist w x y := by
  unfold wdist
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  split_ifs
  · exact h i
  · simp

lemma cost_mono (w v : Fin k → ℝ≥0) (h : ∀ j, w j ≤ v j) (γ : Cpl M) :
    γ.cost w ≤ γ.cost v := by
  unfold Cpl.cost Finsupp.sum
  exact Finset.sum_le_sum fun xy _ => mul_le_mul_of_nonneg_left (wdist_mono w v h _ _) zero_le

lemma offline_scale (w v : Fin k → ℝ≥0) (c : ℝ≥0) (h : ∀ j, v j ≤ c * w j)
    (ρ : List (Config M)) (o : Fin (ρ.length + 1) → Config M) :
    wOfflineCost v ρ o ≤ c * wOfflineCost w ρ o := by
  unfold wOfflineCost
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun s _ => wdist_scale w v c h _ _

/-- The final arithmetic. -/
lemma arith (k : ℕ) (hk : 1 ≤ k) (Sw Sv N V Wk Cv Cw : ℝ) (hSw : Sw ≤ Sv)
    (hS : Sv ≤ N * (10 * 5 ^ (k - 1)) * V) (hL : (N - 1) * (V / 2 ^ k) ≤ Cv)
    (hoff : Cv ≤ 2 ^ (k - 1) * Cw) (hV : V ≤ 2 ^ (k - 1) * Wk) :
    Sw ≤ 20 ^ k * Cw + 10 ^ k * Wk := by
  have hk' : k = (k - 1) + 1 := by omega
  set j := k - 1
  have hc : (0 : ℝ) ≤ 10 * 5 ^ j := by positivity
  have h2 : (0 : ℝ) < 2 ^ k := by positivity
  have e1 : N * (10 * 5 ^ j) * V =
      (10 * 5 ^ j) * V + (2 ^ k * (10 * 5 ^ j)) * ((N - 1) * (V / 2 ^ k)) := by
    field_simp
    ring
  have p10 : (10 : ℝ) ^ j = 5 ^ j * 2 ^ j := by rw [← mul_pow]; norm_num
  have p20 : (20 : ℝ) ^ j = 2 ^ j * 5 ^ j * 2 ^ j := by rw [← mul_pow, ← mul_pow]; norm_num
  have e2 : (10 : ℝ) * 5 ^ j * 2 ^ j = 10 ^ k := by
    rw [hk', pow_succ, p10]; ring
  have e3 : (2 : ℝ) ^ k * (10 * 5 ^ j) * 2 ^ j = 20 ^ k := by
    rw [hk', pow_succ, pow_succ, p20]; ring
  have hc2 : (0 : ℝ) ≤ 2 ^ k * (10 * 5 ^ j) := by positivity
  calc Sw ≤ (10 * 5 ^ j) * V + (2 ^ k * (10 * 5 ^ j)) * ((N - 1) * (V / 2 ^ k)) := by
        rw [← e1]; linarith
    _ ≤ (10 * 5 ^ j) * (2 ^ j * Wk) + (2 ^ k * (10 * 5 ^ j)) * (2 ^ j * Cw) :=
        add_le_add (mul_le_mul_of_nonneg_left hV hc)
          (mul_le_mul_of_nonneg_left (hL.trans hoff) hc2)
    _ = 20 ^ k * Cw + 10 ^ k * Wk := by rw [← e2, ← e3]; ring

end GeneralizedUniformServer.Dev.WB.PartF
end
end

section
set_option autoImplicit false
open scoped NNReal
noncomputable section

end
end

section
set_option autoImplicit false
open scoped NNReal
noncomputable section
namespace GeneralizedUniformServer.Dev.WB.PartM
open GeneralizedUniformServer.UnitWeights GeneralizedUniformServer.UnitWeights.Supplement
open GeneralizedUniformServer.Dev.WB
variable {k : ℕ} {M : Fin k → Type*}
/-!
# Part M, core: linear structure of couplings, the master's steps, support and online property.
-/
/-! ## Linear structure of couplings (copied from Part S) -/
lemma fst_add (γ γ' : Cpl M) : (γ + γ').fst = γ.fst + γ'.fst := Finsupp.mapDomain_add

lemma snd_add (γ γ' : Cpl M) : (γ + γ').snd = γ.snd + γ'.snd := Finsupp.mapDomain_add

lemma fst_zero : (0 : Cpl M).fst = 0 := Finsupp.mapDomain_zero

lemma snd_zero : (0 : Cpl M).snd = 0 := Finsupp.mapDomain_zero

lemma fst_smul (c : ℝ≥0) (γ : Cpl M) : (c • γ).fst = c • γ.fst := Finsupp.mapDomain_smul _ _

lemma snd_smul (c : ℝ≥0) (γ : Cpl M) : (c • γ).snd = c • γ.snd := Finsupp.mapDomain_smul _ _

lemma fst_sum {α : Type*} (s : Finset α) (g : α → Cpl M) :
    (∑ a ∈ s, g a).fst = ∑ a ∈ s, (g a).fst := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [fst_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, fst_add, ih]

lemma snd_sum {α : Type*} (s : Finset α) (g : α → Cpl M) :
    (∑ a ∈ s, g a).snd = ∑ a ∈ s, (g a).snd := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [snd_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, snd_add, ih]

lemma fst_single (x y : Config M) (c : ℝ≥0) :
    Cpl.fst (Finsupp.single (x, y) c : Cpl M) = Finsupp.single x c := Finsupp.mapDomain_single

lemma snd_single (x y : Config M) (c : ℝ≥0) :
    Cpl.snd (Finsupp.single (x, y) c : Cpl M) = Finsupp.single y c := Finsupp.mapDomain_single

end GeneralizedUniformServer.Dev.WB.PartM
end
end

section
set_option autoImplicit false
open scoped NNReal
noncomputable section
namespace GeneralizedUniformServer.Dev.WB.PartM
open GeneralizedUniformServer.UnitWeights GeneralizedUniformServer.UnitWeights.Supplement
open GeneralizedUniformServer.Dev.WB
variable {k : ℕ} {M : Fin k → Type*}
variable (v : Fin k → ℝ≥0)
lemma cost_zero : Cpl.cost v (0 : Cpl M) = 0 := by simp [Cpl.cost]

lemma cost_add (γ γ' : Cpl M) : (γ + γ').cost v = γ.cost v + γ'.cost v := by
  unfold Cpl.cost
  exact Finsupp.sum_add_index' (fun _ => zero_mul _) (fun _ _ _ => add_mul _ _ _)

lemma cost_smul (c : ℝ≥0) (γ : Cpl M) : (c • γ).cost v = c * γ.cost v := by
  unfold Cpl.cost
  rw [Finsupp.sum_smul_index' (fun _ => zero_mul _), Finsupp.mul_sum]
  simp [smul_eq_mul, mul_assoc]

lemma cost_sum {α : Type*} (s : Finset α) (g : α → Cpl M) :
    (∑ a ∈ s, g a).cost v = ∑ a ∈ s, (g a).cost v := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [cost_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, cost_add, ih]

lemma cost_single (x y : Config M) (c : ℝ≥0) :
    Cpl.cost v (Finsupp.single (x, y) c : Cpl M) = c * wdist v x y := by
  unfold Cpl.cost
  rw [Finsupp.sum_single_index (zero_mul _)]

end GeneralizedUniformServer.Dev.WB.PartM
end
end

section
set_option autoImplicit false
open scoped NNReal
noncomputable section
namespace GeneralizedUniformServer.Dev.WB.PartM
open GeneralizedUniformServer.UnitWeights GeneralizedUniformServer.UnitWeights.Supplement
open GeneralizedUniformServer.Dev.WB
variable {k : ℕ} {M : Fin k → Type*}
lemma mass_fst (γ : Cpl M) : mass γ.fst = mass γ := by
  unfold mass Cpl.fst
  exact Finsupp.sum_mapDomain_index (fun _ => rfl) (fun _ _ _ => rfl)

lemma mass_snd (γ : Cpl M) : mass γ.snd = mass γ := by
  unfold mass Cpl.snd
  exact Finsupp.sum_mapDomain_index (fun _ => rfl) (fun _ _ _ => rfl)

lemma mass_single {α : Type*} (a : α) (c : ℝ≥0) : mass (Finsupp.single a c) = c := by
  unfold mass
  exact Finsupp.sum_single_index rfl

lemma mass_eq_sum {α : Type*} (μ : α →₀ ℝ≥0) : mass μ = ∑ y ∈ μ.support, μ y := rfl

lemma mass_zero {α : Type*} : mass (0 : α →₀ ℝ≥0) = 0 := by simp [mass]

lemma mass_add {α : Type*} (μ ν : α →₀ ℝ≥0) : mass (μ + ν) = mass μ + mass ν := by
  unfold mass
  exact Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl)

lemma mass_smul {α : Type*} (c : ℝ≥0) (μ : α →₀ ℝ≥0) : mass (c • μ) = c * mass μ := by
  unfold mass
  rw [Finsupp.sum_smul_index' (fun _ => rfl), Finsupp.mul_sum]
  rfl

lemma mass_sum {α β : Type*} (s : Finset α) (g : α → β →₀ ℝ≥0) :
    mass (∑ a ∈ s, g a) = ∑ a ∈ s, mass (g a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [mass_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, mass_add, ih]

lemma mem_support_snd {γ : Cpl M} {y : Config M} (h : y ∈ γ.snd.support) :
    ∃ xy ∈ γ.support, xy.2 = y := by
  classical
  have := Finsupp.mapDomain_support (f := Prod.snd) (s := γ) h
  simpa using this

lemma mem_support_sum_smul {α β : Type*} (s : Finset α) (c : α → ℝ≥0) (g : α → β →₀ ℝ≥0)
    {b : β} (h : b ∈ (∑ a ∈ s, c a • g a).support) : ∃ a ∈ s, b ∈ (g a).support := by
  classical
  have h1 := Finsupp.support_finsetSum (s := s) (f := fun a => c a • g a) h
  simp only [Finset.mem_biUnion] at h1
  obtain ⟨a, ha, hb⟩ := h1
  exact ⟨a, ha, Finsupp.support_smul hb⟩

/-! ## Chains (copied from Part S) -/
@[simp] lemma isChainD_cons (μ : Config M →₀ ℝ≥0) (γ : Cpl M) (l : List (Cpl M)) :
    IsChainD μ (γ :: l) ↔ γ.fst = μ ∧ IsChainD γ.snd l := Iff.rfl

lemma mass_of_mem_chain {μ : Config M →₀ ℝ≥0} {l : List (Cpl M)} (h : IsChainD μ l)
    {γ : Cpl M} (hγ : γ ∈ l) : mass γ = mass μ := by
  induction l generalizing μ with
  | nil => simp at hγ
  | cons γ' l ih =>
    rw [isChainD_cons] at h
    rcases List.mem_cons.1 hγ with rfl | hγ
    · rw [← mass_fst, h.1]
    · rw [ih h.2 hγ, mass_snd, ← mass_fst, h.1]

lemma getD_cons_succ (γ : Cpl M) (l : List (Cpl M)) (t : ℕ) :
    (γ :: l).getD (t + 1) 0 = l.getD t 0 := by simp

lemma getD_cons_zero (γ : Cpl M) (l : List (Cpl M)) : (γ :: l).getD 0 0 = γ := by simp

lemma chain_getD_zero {μ : Config M →₀ ℝ≥0} {l : List (Cpl M)} (h : IsChainD μ l)
    (hl : 0 < l.length) : (l.getD 0 0).fst = μ := by
  cases l with
  | nil => simp at hl
  | cons γ l => exact h.1

lemma chain_getD_succ {μ : Config M →₀ ℝ≥0} {l : List (Cpl M)} (h : IsChainD μ l)
    {t : ℕ} (ht : t + 1 < l.length) : (l.getD (t + 1) 0).fst = (l.getD t 0).snd := by
  induction l generalizing μ t with
  | nil => simp at ht
  | cons γ l ih =>
    rw [isChainD_cons] at h
    rw [getD_cons_succ]
    cases t with
    | zero =>
      rw [getD_cons_zero]
      exact chain_getD_zero h.2 (by simp at ht; omega)
    | succ t =>
      rw [getD_cons_succ]
      exact ih h.2 (by simp at ht; omega)

lemma isChainD_of_getD (μ : Config M →₀ ℝ≥0) (l : List (Cpl M))
    (h : ∀ t < l.length, (l.getD t 0).fst = if t = 0 then μ else (l.getD (t - 1) 0).snd) :
    IsChainD μ l := by
  induction l generalizing μ with
  | nil => trivial
  | cons γ l ih =>
    refine ⟨by simpa using h 0 (by simp), ih _ fun t ht => ?_⟩
    have := h (t + 1) (by simp; omega)
    rw [getD_cons_succ] at this
    rw [this]
    cases t with
    | zero => simp
    | succ t => simp

lemma chain_mass_getD {μ : Config M →₀ ℝ≥0} {l : List (Cpl M)} (h : IsChainD μ l)
    {t : ℕ} (ht : t < l.length) : mass (l.getD t 0) = mass μ := by
  apply mass_of_mem_chain h
  rw [List.getD_eq_getElem _ _ ht]
  exact List.getElem_mem ht

lemma getD_eq_zero_of_le (l : List (Cpl M)) {t : ℕ} (ht : l.length ≤ t) : l.getD t 0 = 0 :=
  List.getD_eq_default _ _ ht

lemma getD_take (l : List (Cpl M)) {s t : ℕ} (h : t < s) :
    (l.take s).getD t 0 = l.getD t 0 := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_take, h, if_true]

lemma chainCost_eq_sum (v : Fin k → ℝ≥0) (l : List (Cpl M)) :
    chainCost v l = ∑ t ∈ Finset.range l.length, (l.getD t 0).cost v := by
  induction l with
  | nil => simp [chainCost]
  | cons γ l ih =>
    have : chainCost v (γ :: l) = γ.cost v + chainCost v l := by simp [chainCost]
    rw [this, ih, List.length_cons, Finset.sum_range_succ']
    simp [add_comm]

/-! ## Product couplings -/
lemma prodC_eq (μ ν : Config M →₀ ℝ≥0) :
    prodC μ ν = ∑ x ∈ μ.support, ∑ y ∈ ν.support, Finsupp.single (x, y) (μ x * ν y) := rfl

lemma sum_smul_single (μ : Config M →₀ ℝ≥0) :
    ∑ x ∈ μ.support, Finsupp.single x (μ x) = μ := Finsupp.sum_single μ

lemma prodC_fst (μ ν : Config M →₀ ℝ≥0) : (prodC μ ν).fst = mass ν • μ := by
  rw [prodC_eq, fst_sum]
  simp_rw [fst_sum, fst_single]
  conv_rhs => rw [← sum_smul_single μ, Finset.smul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← Finsupp.single_finsetSum, ← Finset.mul_sum, Finsupp.smul_single, smul_eq_mul,
    mass_eq_sum, mul_comm]

lemma prodC_snd (μ ν : Config M →₀ ℝ≥0) : (prodC μ ν).snd = mass μ • ν := by
  rw [prodC_eq, snd_sum]
  simp_rw [snd_sum, snd_single]
  rw [Finset.sum_comm]
  conv_rhs => rw [← sum_smul_single ν, Finset.smul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [← Finsupp.single_finsetSum, ← Finset.sum_mul, Finsupp.smul_single, smul_eq_mul,
    mass_eq_sum]

lemma mem_support_prodC {μ ν : Config M →₀ ℝ≥0} {xy : Config M × Config M}
    (h : xy ∈ (prodC μ ν).support) : xy.1 ∈ μ.support ∧ xy.2 ∈ ν.support := by
  classical
  rw [prodC_eq] at h
  have h1 := Finsupp.support_finsetSum h
  simp only [Finset.mem_biUnion] at h1
  obtain ⟨x, hx, h2⟩ := h1
  have h3 := Finsupp.support_finsetSum h2
  simp only [Finset.mem_biUnion] at h3
  obtain ⟨y, hy, h4⟩ := h3
  have h5 := Finsupp.support_single_subset h4
  rw [Finset.mem_singleton] at h5
  subst h5
  exact ⟨hx, hy⟩

lemma prodC_cost_le (v : Fin k → ℝ≥0) (Δ : ℝ≥0) (B : Set (Config M))
    (hB : ∀ z ∈ B, ∀ z' ∈ B, wdist v z z' ≤ Δ) (μ ν : Config M →₀ ℝ≥0)
    (hμ : ∀ x ∈ μ.support, x ∈ B) (hν : ∀ y ∈ ν.support, y ∈ B) :
    (prodC μ ν).cost v ≤ Δ * mass μ * mass ν := by
  rw [prodC_eq, cost_sum, mass_eq_sum, mass_eq_sum, mul_comm Δ, Finset.sum_mul, Finset.sum_mul]
  refine Finset.sum_le_sum fun x hx => ?_
  rw [cost_sum, Finset.mul_sum]
  refine Finset.sum_le_sum fun y hy => ?_
  rw [cost_single]
  calc μ x * ν y * wdist v x y ≤ μ x * ν y * Δ := by
        gcongr; exact hB x (hμ x hx) y (hν y hy)
    _ = μ x * Δ * ν y := by ring

end GeneralizedUniformServer.Dev.WB.PartM
end
end

section
set_option autoImplicit false
open scoped NNReal
noncomputable section
namespace GeneralizedUniformServer.Dev.WB.PartM
open GeneralizedUniformServer.UnitWeights GeneralizedUniformServer.UnitWeights.Supplement
open GeneralizedUniformServer.Dev.WB
variable {k : ℕ} {M : Fin k → Type*}
variable (v : Fin k → ℝ≥0) (Δ : ℝ≥0) {ι : Type*}
/-!
# Part M, steps of the master: online property, support, weights, marginals.
-/
/-- Step `t` of the master. -/
def mstep (y : Config M) (S : Finset ι) (cp : ι → List (Cpl M)) (t : ℕ) : Cpl M :=
  if t = 0 then prodC (Finsupp.single y 1) (mDist v Δ S cp 0)
  else
    (∑ p ∈ S, mKeep v Δ S cp t p • (cp p).getD t 0) +
      prodC (∑ p ∈ S, (mNu v Δ S cp (t - 1) p - mKeep v Δ S cp t p) •
          ((cp p).getD (t - 1) 0).snd)
        (mDist v Δ S cp t)

/-- Total weight `W(t)`. -/
def mW (S : Finset ι) (cp : ι → List (Cpl M)) (t : ℕ) : ℝ≥0 :=
  ∑ q ∈ S, mWeight v Δ (cp q) t

lemma master_eq (y : Config M) (S : Finset ι) (cp : ι → List (Cpl M)) (n : ℕ) :
    master v Δ y S cp n = List.ofFn fun t : Fin n => mstep v Δ y S cp t := rfl

lemma length_master (y : Config M) (S : Finset ι) (cp : ι → List (Cpl M)) (n : ℕ) :
    (master v Δ y S cp n).length = n := by simp [master]

lemma getD_master (y : Config M) (S : Finset ι) (cp : ι → List (Cpl M)) {n t : ℕ}
    (ht : t < n) : (master v Δ y S cp n).getD t 0 = mstep v Δ y S cp t := by
  rw [master_eq, List.getD_eq_getElem _ _ (by simpa using ht), List.getElem_ofFn]

/-! ### Online property -/
lemma cumCost_take (l : List (Cpl M)) {s t : ℕ} (hs : s < t) :
    cumCost v (l.take t) s = cumCost v l s := by
  unfold cumCost
  refine Finset.sum_congr rfl fun r hr => ?_
  rw [Finset.mem_range] at hr
  rw [getD_take _ (by omega)]

lemma mWeight_take (l : List (Cpl M)) {s t : ℕ} (hs : s < t) :
    mWeight v Δ (l.take t) s = mWeight v Δ l s := by
  unfold mWeight
  rw [cumCost_take v l hs]
  have : s < (l.take t).length ↔ s < l.length := by simp; omega
  simp only [this]

lemma mNu_take (S : Finset ι) (cp : ι → List (Cpl M)) {s t : ℕ} (hs : s < t) (p : ι) :
    mNu v Δ S (fun q => (cp q).take t) s p = mNu v Δ S cp s p := by
  unfold mNu
  simp only [mWeight_take v Δ _ hs]

lemma mDist_take (S : Finset ι) (cp : ι → List (Cpl M)) {s t : ℕ} (hs : s < t) :
    mDist v Δ S (fun q => (cp q).take t) s = mDist v Δ S cp s := by
  unfold mDist
  simp only [mNu_take v Δ S cp hs, getD_take _ hs]

lemma mKeep_take (S : Finset ι) (cp : ι → List (Cpl M)) {s t : ℕ} (hs : s < t) (p : ι) :
    mKeep v Δ S (fun q => (cp q).take t) s p = mKeep v Δ S cp s p := by
  unfold mKeep
  have h1 : s < ((cp p).take t).length ↔ s < (cp p).length := by simp; omega
  simp only [h1, mNu_take v Δ S cp (show s - 1 < t by omega), getD_take _ hs]

lemma mstep_take (y : Config M) (S : Finset ι) (cp : ι → List (Cpl M)) {s t : ℕ}
    (hs : s < t) : mstep v Δ y S (fun q => (cp q).take t) s = mstep v Δ y S cp s := by
  unfold mstep
  simp only [mDist_take v Δ S cp hs, mDist_take v Δ S cp (show 0 < t by omega),
    mKeep_take v Δ S cp hs, mNu_take v Δ S cp (show s - 1 < t by omega), getD_take _ hs,
    getD_take _ (show s - 1 < t by omega)]

theorem master_take' (y : Config M) (S : Finset ι) (cp : ι → List (Cpl M)) (n t : ℕ) :
    (master v Δ y S cp n).take t =
      master v Δ y S (fun p => (cp p).take t) (min n t) := by
  apply List.ext_getElem
  · simp [length_master, Nat.min_comm]
  · intro i h1 h2
    simp only [List.getElem_take, master_eq, List.getElem_ofFn]
    simp only [List.length_take, length_master] at h1
    rw [mstep_take v Δ y S cp (by omega)]

/-! ### Support -/
lemma lt_length_of_mem_support {l : List (Cpl M)} {t : ℕ} {xy : Config M × Config M}
    (h : xy ∈ (l.getD t 0).support) : t < l.length := by
  by_contra h'
  rw [getD_eq_zero_of_le _ (not_lt.1 h')] at h
  simp at h

end GeneralizedUniformServer.Dev.WB.PartM
end
end

section
set_option autoImplicit false
open scoped NNReal
noncomputable section
namespace GeneralizedUniformServer.Dev.WB.PartM
open GeneralizedUniformServer.UnitWeights GeneralizedUniformServer.UnitWeights.Supplement
open GeneralizedUniformServer.Dev.WB
variable {k : ℕ} {M : Fin k → Type*}
variable (v : Fin k → ℝ≥0) (Δ : ℝ≥0) {ι : Type*}
variable {y : Config M} {S : Finset ι} {cp : ι → List (Cpl M)} {n : ℕ} {st : ι → Config M}
  {B : Set (Config M)}
/-! ## Cost of each step -/
lemma snd_supp_B (h : MasterHyp v Δ y S cp n st B) {p : ι} (hp : p ∈ S) {s : ℕ} {z : Config M}
    (hz : z ∈ ((cp p).getD s 0).snd.support) : z ∈ B := by
  obtain ⟨xy, hxy, rfl⟩ := mem_support_snd hz
  have hlt := lt_length_of_mem_support hxy
  refine h.supp p hp _ ?_ xy hxy
  rw [List.getD_eq_getElem _ _ hlt]
  exact List.getElem_mem hlt

lemma sum_supp_B (h : MasterHyp v Δ y S cp n st B) (c : ι → ℝ≥0) (s : ℕ) {z : Config M}
    (hz : z ∈ (∑ p ∈ S, c p • ((cp p).getD s 0).snd).support) : z ∈ B := by
  obtain ⟨p, hp, hz⟩ := mem_support_sum_smul _ _ _ hz
  exact snd_supp_B v Δ h hp hz

end GeneralizedUniformServer.Dev.WB.PartM
end
end

section
set_option autoImplicit false
open scoped NNReal
noncomputable section
namespace GeneralizedUniformServer.Dev.WB.PartM
open GeneralizedUniformServer.UnitWeights GeneralizedUniformServer.UnitWeights.Supplement
open GeneralizedUniformServer.Dev.WB
variable {k : ℕ} {M : Fin k → Type*}
variable (v : Fin k → ℝ≥0) (Δ : ℝ≥0) {ι : Type*}
lemma lt_length_of_mem_support_snd {l : List (Cpl M)} {t : ℕ} {z : Config M}
    (h : z ∈ (l.getD t 0).snd.support) : t < l.length := by
  obtain ⟨xy, hxy, _⟩ := mem_support_snd h
  exact lt_length_of_mem_support hxy

lemma mem_support_mDist {S : Finset ι} {cp : ι → List (Cpl M)} {t : ℕ} {z : Config M}
    (h : z ∈ (mDist v Δ S cp t).support) :
    ∃ p ∈ S, t < (cp p).length ∧ ∃ xy' ∈ ((cp p).getD t 0).support, xy'.2 = z := by
  obtain ⟨p, hp, hz⟩ := mem_support_sum_smul _ _ _ h
  exact ⟨p, hp, lt_length_of_mem_support_snd hz, mem_support_snd hz⟩

theorem master_supp' (y : Config M) (S : Finset ι) (cp : ι → List (Cpl M)) (n : ℕ)
    (t : ℕ) (ht : t < n) (xy : Config M × Config M)
    (hxy : xy ∈ ((master v Δ y S cp n).getD t 0).support) :
    ∃ p ∈ S, t < (cp p).length ∧ ∃ xy' ∈ ((cp p).getD t 0).support, xy'.2 = xy.2 := by
  classical
  rw [getD_master v Δ y S cp ht] at hxy
  unfold mstep at hxy
  split_ifs at hxy with h0
  · subst h0
    exact mem_support_mDist v Δ (mem_support_prodC hxy).2
  · rcases Finset.mem_union.1 (Finsupp.support_add hxy) with h | h
    · obtain ⟨p, hp, hz⟩ := mem_support_sum_smul _ _ _ h
      exact ⟨p, hp, lt_length_of_mem_support hz, xy, hz, rfl⟩
    · exact mem_support_mDist v Δ (mem_support_prodC h).2

/-! ### Weights -/
lemma coe_mWeight (l : List (Cpl M)) (t : ℕ) :
    (mWeight v Δ l t : ℝ) =
      if t < l.length then Real.exp (-(cumCost v l t : ℝ) / (Δ : ℝ)) else 0 := by
  unfold mWeight
  split_ifs
  · exact Real.coe_toNNReal _ (Real.exp_pos _).le
  · rfl

lemma mWeight_le_one (l : List (Cpl M)) (t : ℕ) : mWeight v Δ l t ≤ 1 := by
  unfold mWeight
  split_ifs
  · rw [Real.toNNReal_le_one, Real.exp_le_one_iff, neg_div, neg_nonpos]
    positivity
  · exact zero_le_one

lemma mWeight_pos (l : List (Cpl M)) {t : ℕ} (ht : t < l.length) : 0 < mWeight v Δ l t := by
  unfold mWeight
  rw [if_pos ht]
  exact Real.toNNReal_pos.2 (Real.exp_pos _)

lemma mWeight_eq_zero (l : List (Cpl M)) {t : ℕ} (ht : l.length ≤ t) : mWeight v Δ l t = 0 := by
  unfold mWeight
  rw [if_neg (by omega)]

lemma mWeight_succ (l : List (Cpl M)) {t : ℕ} (ht : t + 1 < l.length) :
    mWeight v Δ l (t + 1) =
      mWeight v Δ l t * Real.toNNReal (Real.exp (-((l.getD (t + 1) 0).cost v : ℝ) / (Δ : ℝ))) := by
  unfold mWeight
  rw [if_pos ht, if_pos (by omega), ← Real.toNNReal_mul (Real.exp_pos _).le, ← Real.exp_add]
  congr 2
  unfold cumCost
  rw [Finset.sum_range_succ]
  push_cast
  ring

lemma mKeep_eq (S : Finset ι) (cp : ι → List (Cpl M)) {t : ℕ} (ht : 1 ≤ t) (p : ι) :
    mKeep v Δ S cp t p = mWeight v Δ (cp p) t / mW v Δ S cp (t - 1) := by
  unfold mKeep
  split_ifs with h
  · obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
    rw [mWeight_succ v Δ _ h, Nat.add_sub_cancel]
    unfold mNu mW
    rw [div_mul_eq_mul_div]
  · rw [mWeight_eq_zero v Δ _ (by omega), zero_div]

lemma mKeep_le (S : Finset ι) (cp : ι → List (Cpl M)) (t : ℕ) (p : ι) :
    mKeep v Δ S cp t p ≤ mNu v Δ S cp (t - 1) p := by
  unfold mKeep
  split_ifs
  · refine mul_le_of_le_one_right (zero_le) ?_
    rw [Real.toNNReal_le_one, Real.exp_le_one_iff, neg_div, neg_nonpos]
    positivity
  · exact zero_le

lemma mNu_eq_zero (S : Finset ι) (cp : ι → List (Cpl M)) {t : ℕ} {p : ι}
    (ht : (cp p).length ≤ t) : mNu v Δ S cp t p = 0 := by
  unfold mNu
  rw [mWeight_eq_zero v Δ _ ht, zero_div]

lemma sum_mNu (S : Finset ι) (cp : ι → List (Cpl M)) {t : ℕ} (hW : 0 < mW v Δ S cp t) :
    ∑ p ∈ S, mNu v Δ S cp t p = 1 := by
  unfold mNu
  rw [← Finset.sum_div]
  exact div_self hW.ne'

lemma sum_mKeep (S : Finset ι) (cp : ι → List (Cpl M)) {t : ℕ} (ht : 1 ≤ t) :
    ∑ p ∈ S, mKeep v Δ S cp t p = mW v Δ S cp t / mW v Δ S cp (t - 1) := by
  simp only [mKeep_eq v Δ S cp ht]
  rw [← Finset.sum_div]
  rfl

lemma mKeep_eq_mul (S : Finset ι) (cp : ι → List (Cpl M)) {t : ℕ} (ht : 1 ≤ t)
    (hW : 0 < mW v Δ S cp t) (p : ι) :
    mKeep v Δ S cp t p = (mW v Δ S cp t / mW v Δ S cp (t - 1)) * mNu v Δ S cp t p := by
  rw [mKeep_eq v Δ S cp ht]
  unfold mNu
  change _ = _ * (_ / mW v Δ S cp t)
  rw [div_mul_div_comm, mul_comm (mW v Δ S cp t), mul_div_mul_right _ _ hW.ne']

lemma mW_le_card (S : Finset ι) (cp : ι → List (Cpl M)) (t : ℕ) : mW v Δ S cp t ≤ S.card := by
  unfold mW
  calc ∑ q ∈ S, mWeight v Δ (cp q) t ≤ ∑ _q ∈ S, (1 : ℝ≥0) :=
        Finset.sum_le_sum fun q _ => mWeight_le_one v Δ _ _
    _ = S.card := by simp

lemma mWeight_le_mW (S : Finset ι) (cp : ι → List (Cpl M)) (t : ℕ) {p : ι} (hp : p ∈ S) :
    mWeight v Δ (cp p) t ≤ mW v Δ S cp t :=
  Finset.single_le_sum (f := fun q => mWeight v Δ (cp q) t) (fun _ _ => zero_le) hp

end GeneralizedUniformServer.Dev.WB.PartM
end
end

section
set_option autoImplicit false
open scoped NNReal
noncomputable section
namespace GeneralizedUniformServer.Dev.WB.PartM
open GeneralizedUniformServer.UnitWeights GeneralizedUniformServer.UnitWeights.Supplement
open GeneralizedUniformServer.Dev.WB
variable {k : ℕ} {M : Fin k → Type*}
variable (v : Fin k → ℝ≥0) (Δ : ℝ≥0) {ι : Type*}
variable {y : Config M} {S : Finset ι} {cp : ι → List (Cpl M)} {n : ℕ} {st : ι → Config M}
  {B : Set (Config M)}
/-!
# Part M, marginals of the master under `MasterHyp`: the master is a chain.
-/
lemma mass_getD_cp (h : MasterHyp v Δ y S cp n st B) {p : ι} (hp : p ∈ S) (t : ℕ) :
    mass ((cp p).getD t 0) = if t < (cp p).length then 1 else 0 := by
  split_ifs with ht
  · rw [chain_mass_getD (h.chain p hp) ht, mass_single]
  · rw [getD_eq_zero_of_le _ (not_lt.1 ht)]
    exact mass_zero

lemma mW_pos (h : MasterHyp v Δ y S cp n st B) {t : ℕ} (ht : t < n) : 0 < mW v Δ S cp t := by
  rcases h.len_eq with h0 | ⟨j, hj, hjn⟩
  · omega
  · exact lt_of_lt_of_le (mWeight_pos v Δ _ (by omega)) (mWeight_le_mW v Δ S cp t hj)

lemma mass_mDist (h : MasterHyp v Δ y S cp n st B) {t : ℕ} (ht : t < n) :
    mass (mDist v Δ S cp t) = 1 := by
  unfold mDist
  rw [mass_sum]
  simp only [mass_smul, mass_snd]
  rw [← sum_mNu v Δ S cp (mW_pos v Δ h ht)]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [mass_getD_cp v Δ h hp]
  split_ifs with h1
  · rw [mul_one]
  · rw [mul_zero, mNu_eq_zero v Δ S cp (not_lt.1 h1)]

lemma cost_mstep_zero (h : MasterHyp v Δ y S cp n st B) (hn : 0 < n) :
    (mstep v Δ y S cp 0).cost v ≤ Δ := by
  unfold mstep
  rw [if_pos rfl]
  refine (prodC_cost_le v Δ B h.diam _ _ ?_ ?_).trans ?_
  · intro x hx
    rw [Finset.mem_singleton.1 (Finsupp.support_single_subset hx)]
    exact h.hy
  · intro z hz
    exact sum_supp_B v Δ h _ 0 hz
  · rw [mass_single, mass_mDist v Δ h hn, mul_one, mul_one]

/-- The part of the mass that is resampled at step `t`. -/
def mP (S : Finset ι) (cp : ι → List (Cpl M)) (t : ℕ) : Config M →₀ ℝ≥0 :=
  ∑ p ∈ S, (mNu v Δ S cp (t - 1) p - mKeep v Δ S cp t p) • ((cp p).getD (t - 1) 0).snd

lemma mass_mP (h : MasterHyp v Δ y S cp n st B) {t : ℕ} (ht1 : 1 ≤ t) (ht : t < n) :
    mass (mP v Δ S cp t) = 1 - mW v Δ S cp t / mW v Δ S cp (t - 1) := by
  unfold mP
  rw [mass_sum]
  simp only [mass_smul, mass_snd]
  rw [← sum_mNu v Δ S cp (mW_pos v Δ h (show t - 1 < n by omega)), ← sum_mKeep v Δ S cp ht1,
    ← Finset.sum_tsub_distrib _ (fun p _ => mKeep_le v Δ S cp t p)]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [mass_getD_cp v Δ h hp]
  split_ifs with h1
  · rw [mul_one]
  · rw [mul_zero, mNu_eq_zero v Δ S cp (not_lt.1 h1), zero_tsub]

lemma zeta_le_one (h : MasterHyp v Δ y S cp n st B) {t : ℕ} (ht1 : 1 ≤ t) (ht : t < n) :
    mW v Δ S cp t / mW v Δ S cp (t - 1) ≤ 1 := by
  rw [← sum_mKeep v Δ S cp ht1, ← sum_mNu v Δ S cp (mW_pos v Δ h (show t - 1 < n by omega))]
  exact Finset.sum_le_sum fun p _ => mKeep_le v Δ S cp t p

lemma mstep_pos (y : Config M) (S : Finset ι) (cp : ι → List (Cpl M)) {t : ℕ} (ht1 : 1 ≤ t) :
    mstep v Δ y S cp t =
      (∑ p ∈ S, mKeep v Δ S cp t p • (cp p).getD t 0) + prodC (mP v Δ S cp t) (mDist v Δ S cp t) := by
  unfold mstep
  rw [if_neg (by omega)]
  rfl

lemma cost_mstep (h : MasterHyp v Δ y S cp n st B) {t : ℕ} (ht1 : 1 ≤ t) (ht : t < n) :
    ((mstep v Δ y S cp t).cost v : ℝ) ≤
      2 * Δ * (Real.log (mW v Δ S cp (t - 1)) - Real.log (mW v Δ S cp t)) := by
  have hle : (mstep v Δ y S cp t).cost v ≤
      ∑ p ∈ S, mKeep v Δ S cp t p * ((cp p).getD t 0).cost v +
        Δ * (1 - mW v Δ S cp t / mW v Δ S cp (t - 1)) := by
    rw [mstep_pos v Δ y S cp ht1, cost_add, cost_sum]
    simp only [cost_smul]
    gcongr
    refine (prodC_cost_le v Δ B h.diam _ _ ?_ ?_).trans ?_
    · intro z hz
      exact sum_supp_B v Δ h _ _ hz
    · intro z hz
      exact sum_supp_B v Δ h _ _ hz
    · rw [mass_mP v Δ h ht1 ht, mass_mDist v Δ h ht, mul_one]
  have hz1 := zeta_le_one v Δ h ht1 ht
  have hW0 := mW_pos v Δ h (show t - 1 < n by omega)
  have hW1 := mW_pos v Δ h ht
  refine (NNReal.coe_le_coe.2 hle).trans ?_
  push_cast [NNReal.coe_sub hz1]
  simp only [mKeep_eq v Δ S cp ht1, NNReal.coe_div]
  unfold mW
  push_cast
  have hΔ : (0 : ℝ) < Δ := h.pos
  refine real_step S (fun p => (mWeight v Δ (cp p) (t - 1) : ℝ))
    (fun p => (mWeight v Δ (cp p) t : ℝ)) (fun p => (((cp p).getD t 0).cost v : ℝ)) Δ hΔ
    (fun p _ => NNReal.coe_nonneg _) (fun p _ => NNReal.coe_nonneg _) ?_ ?_ ?_
  · intro p _
    by_cases ha : t < (cp p).length
    · have hs := mWeight_succ v Δ (cp p) (t := t - 1) (by omega)
      rw [Nat.sub_add_cancel ht1] at hs
      rw [hs, NNReal.coe_mul, Real.coe_toNNReal _ (Real.exp_pos _).le, mul_assoc,
        ← Real.exp_add, neg_div, neg_add_cancel, Real.exp_zero, mul_one]
    · rw [mWeight_eq_zero v Δ _ (not_lt.1 ha), NNReal.coe_zero, zero_mul]
      exact NNReal.coe_nonneg _
  · have := hW0
    unfold mW at this
    exact_mod_cast this
  · have := hW1
    unfold mW at this
    exact_mod_cast this

lemma snd_mstep (h : MasterHyp v Δ y S cp n st B) {t : ℕ} (ht : t < n) :
    (mstep v Δ y S cp t).snd = mDist v Δ S cp t := by
  rcases Nat.eq_zero_or_pos t with h0 | h0
  · subst h0
    unfold mstep
    rw [if_pos rfl, prodC_snd, mass_single, one_smul]
  · rw [mstep_pos v Δ y S cp h0, snd_add, prodC_snd, mass_mP v Δ h h0 ht, snd_sum]
    simp only [snd_smul]
    simp only [mKeep_eq_mul v Δ S cp h0 (mW_pos v Δ h ht), mul_smul]
    rw [← Finset.smul_sum]
    have hD : ∑ p ∈ S, mNu v Δ S cp t p • ((cp p).getD t 0).snd = mDist v Δ S cp t := rfl
    rw [hD, ← add_smul, add_tsub_cancel_of_le (zeta_le_one v Δ h h0 ht), one_smul]

lemma fst_mstep_zero (h : MasterHyp v Δ y S cp n st B) (hn : 0 < n) :
    (mstep v Δ y S cp 0).fst = Finsupp.single y 1 := by
  unfold mstep
  rw [if_pos rfl, prodC_fst, mass_mDist v Δ h hn, one_smul]

lemma fst_mstep (h : MasterHyp v Δ y S cp n st B) {t : ℕ} (ht1 : 1 ≤ t) (ht : t < n) :
    (mstep v Δ y S cp t).fst = mDist v Δ S cp (t - 1) := by
  rw [mstep_pos v Δ y S cp ht1, fst_add, prodC_fst, mass_mDist v Δ h ht, one_smul, fst_sum]
  unfold mP mDist
  simp only [fst_smul]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun p hp => ?_
  by_cases ha : t < (cp p).length
  · have hc := chain_getD_succ (h.chain p hp) (t := t - 1) (by omega)
    rw [Nat.sub_add_cancel ht1] at hc
    rw [hc, ← add_smul, add_tsub_cancel_of_le (mKeep_le v Δ S cp t p)]
  · have : mKeep v Δ S cp t p = 0 := by unfold mKeep; rw [if_neg ha]
    rw [this, zero_smul, zero_add, tsub_zero]

theorem master_chain' (h : MasterHyp v Δ y S cp n st B) :
    IsChainD (Finsupp.single y 1) (master v Δ y S cp n) := by
  apply isChainD_of_getD
  intro t ht
  rw [length_master] at ht
  rw [getD_master v Δ y S cp ht]
  split_ifs with h0
  · subst h0
    exact fst_mstep_zero v Δ h ht
  · rw [fst_mstep v Δ h (by omega) ht, getD_master v Δ y S cp (show t - 1 < n by omega),
      snd_mstep v Δ h (show t - 1 < n by omega)]

end GeneralizedUniformServer.Dev.WB.PartM
end
end

section
set_option autoImplicit false
open scoped NNReal
noncomputable section
namespace GeneralizedUniformServer.Dev.WB.PartM
open GeneralizedUniformServer.UnitWeights GeneralizedUniformServer.UnitWeights.Supplement
open GeneralizedUniformServer.Dev.WB
variable {k : ℕ} {M : Fin k → Type*}
variable (v : Fin k → ℝ≥0) (Δ : ℝ≥0) {ι : Type*}
/-! ## The four theorems -/
theorem master_chain (y : Config M) (S : Finset ι) (cp : ι → List (Cpl M)) (n : ℕ)
    (st : ι → Config M) (B : Set (Config M)) (h : MasterHyp v Δ y S cp n st B) :
    IsChainD (Finsupp.single y 1) (master v Δ y S cp n) :=
  master_chain' v Δ h

end GeneralizedUniformServer.Dev.WB.PartM
end
end

section
open scoped NNReal
noncomputable section
namespace GeneralizedUniformServer.Dev.WB
open GeneralizedUniformServer.UnitWeights GeneralizedUniformServer.UnitWeights.Supplement
variable {k : ℕ} {M : Fin k → Type*}
variable (v : Fin k → ℝ≥0) (Δ : ℝ≥0) {ι : Type*}
alias master_chain := GeneralizedUniformServer.Dev.WB.PartM.master_chain

end GeneralizedUniformServer.Dev.WB
end
end

section
set_option autoImplicit false
open scoped NNReal
noncomputable section
namespace GeneralizedUniformServer.Dev.WB.PartM
open GeneralizedUniformServer.UnitWeights GeneralizedUniformServer.UnitWeights.Supplement
open GeneralizedUniformServer.Dev.WB
variable {k : ℕ} {M : Fin k → Type*}
variable (v : Fin k → ℝ≥0) (Δ : ℝ≥0) {ι : Type*}
theorem master_supp (y : Config M) (S : Finset ι) (cp : ι → List (Cpl M)) (n : ℕ)
    (st : ι → Config M) (B : Set (Config M)) (h : MasterHyp v Δ y S cp n st B)
    (t : ℕ) (ht : t < n) (xy : Config M × Config M)
    (hxy : xy ∈ ((master v Δ y S cp n).getD t 0).support) :
    ∃ p ∈ S, t < (cp p).length ∧ ∃ xy' ∈ ((cp p).getD t 0).support, xy'.2 = xy.2 :=
  master_supp' v Δ y S cp n t ht xy hxy

end GeneralizedUniformServer.Dev.WB.PartM
end
end

section
open scoped NNReal
noncomputable section
namespace GeneralizedUniformServer.Dev.WB
open GeneralizedUniformServer.UnitWeights GeneralizedUniformServer.UnitWeights.Supplement
variable {k : ℕ} {M : Fin k → Type*}
variable (v : Fin k → ℝ≥0) (Δ : ℝ≥0) {ι : Type*}
alias master_supp := GeneralizedUniformServer.Dev.WB.PartM.master_supp

end GeneralizedUniformServer.Dev.WB
end
end

section
set_option autoImplicit false
open scoped NNReal
noncomputable section
namespace GeneralizedUniformServer.Dev.WB.PartM
open GeneralizedUniformServer.UnitWeights GeneralizedUniformServer.UnitWeights.Supplement
open GeneralizedUniformServer.Dev.WB
variable {k : ℕ} {M : Fin k → Type*}
variable (v : Fin k → ℝ≥0) (Δ : ℝ≥0) {ι : Type*}
theorem master_cost (y : Config M) (S : Finset ι) (cp : ι → List (Cpl M)) (n : ℕ)
    (st : ι → Config M) (B : Set (Config M)) (h : MasterHyp v Δ y S cp n st B)
    (j : ι) (hj : j ∈ S) (hjn : (cp j).length = n) :
    (chainCost v (master v Δ y S cp n) : ℝ) ≤
      Δ + 2 * Δ * Real.log S.card + 2 * chainCost v (cp j) := by
  have hΔ : (0 : ℝ) < Δ := h.pos
  have hcard : (1 : ℝ) ≤ S.card := by exact_mod_cast h.nonempty.card_pos
  have hlogS : 0 ≤ Real.log S.card := Real.log_nonneg hcard
  rw [chainCost_eq_sum, length_master]
  rcases Nat.eq_zero_or_pos n with h0 | hn
  · subst h0
    simp only [Finset.range_zero, Finset.sum_empty, NNReal.coe_zero]
    positivity
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [Finset.sum_range_succ', NNReal.coe_add, NNReal.coe_sum]
  have hsum : ∑ s ∈ Finset.range m, ((((master v Δ y S cp (m + 1)).getD (s + 1) 0).cost v : ℝ≥0) : ℝ)
      ≤ ∑ s ∈ Finset.range m, 2 * Δ * (Real.log (mW v Δ S cp s) - Real.log (mW v Δ S cp (s + 1))) := by
    refine Finset.sum_le_sum fun s hs => ?_
    rw [Finset.mem_range] at hs
    rw [getD_master v Δ y S cp (show s + 1 < m + 1 by omega)]
    have := cost_mstep v Δ h (t := s + 1) (by omega) (by omega)
    simpa using this
  rw [← Finset.mul_sum, Finset.sum_range_sub'] at hsum
  have h0c : ((((master v Δ y S cp (m + 1)).getD 0 0).cost v : ℝ≥0) : ℝ) ≤ Δ := by
    rw [getD_master v Δ y S cp (show 0 < m + 1 by omega)]
    exact_mod_cast cost_mstep_zero v Δ h hn
  -- the two ends of the telescope
  have hW0 := mW_pos v Δ h (show 0 < m + 1 by omega)
  have hWm := mW_pos v Δ h (show m < m + 1 by omega)
  have hlog0 : Real.log (mW v Δ S cp 0) ≤ Real.log S.card :=
    Real.log_le_log (by exact_mod_cast hW0) (by exact_mod_cast mW_le_card v Δ S cp 0)
  have hjw : (mWeight v Δ (cp j) m : ℝ) = Real.exp (-(cumCost v (cp j) m : ℝ) / Δ) := by
    rw [coe_mWeight, if_pos (by omega)]
  have hlogm : -(cumCost v (cp j) m : ℝ) / Δ ≤ Real.log (mW v Δ S cp m) := by
    rw [← Real.log_exp (-(cumCost v (cp j) m : ℝ) / Δ), ← hjw]
    exact Real.log_le_log (by rw [hjw]; exact Real.exp_pos _)
      (by exact_mod_cast mWeight_le_mW v Δ S cp m hj)
  have hcum : cumCost v (cp j) m = chainCost v (cp j) := by
    rw [chainCost_eq_sum, hjn]
    rfl
  rw [hcum] at hlogm
  have hdiv : Δ * (-(chainCost v (cp j) : ℝ) / Δ) = -(chainCost v (cp j) : ℝ) := by
    field_simp
  nlinarith

end GeneralizedUniformServer.Dev.WB.PartM
end
end

section
open scoped NNReal
noncomputable section
namespace GeneralizedUniformServer.Dev.WB
open GeneralizedUniformServer.UnitWeights GeneralizedUniformServer.UnitWeights.Supplement
variable {k : ℕ} {M : Fin k → Type*}
variable (v : Fin k → ℝ≥0) (Δ : ℝ≥0) {ι : Type*}
alias master_cost := GeneralizedUniformServer.Dev.WB.PartM.master_cost

end GeneralizedUniformServer.Dev.WB
end
end

section
set_option autoImplicit false
open scoped NNReal
noncomputable section
namespace GeneralizedUniformServer.Dev.WB.PartM
open GeneralizedUniformServer.UnitWeights GeneralizedUniformServer.UnitWeights.Supplement
open GeneralizedUniformServer.Dev.WB
variable {k : ℕ} {M : Fin k → Type*}
variable (v : Fin k → ℝ≥0) (Δ : ℝ≥0) {ι : Type*}
theorem master_take (y : Config M) (S : Finset ι) (cp : ι → List (Cpl M)) (n t : ℕ) :
    (master v Δ y S cp n).take t =
      master v Δ y S (fun p => (cp p).take t) (min n t) :=
  master_take' v Δ y S cp n t

end GeneralizedUniformServer.Dev.WB.PartM
end
end

section
open scoped NNReal
noncomputable section
namespace GeneralizedUniformServer.Dev.WB
open GeneralizedUniformServer.UnitWeights GeneralizedUniformServer.UnitWeights.Supplement
variable {k : ℕ} {M : Fin k → Type*}
variable (v : Fin k → ℝ≥0) (Δ : ℝ≥0) {ι : Type*}
alias master_take := GeneralizedUniformServer.Dev.WB.PartM.master_take

end GeneralizedUniformServer.Dev.WB
end
end

section
set_option autoImplicit false
open scoped NNReal
noncomputable section
namespace GeneralizedUniformServer.Dev.WB.PartM
open GeneralizedUniformServer.UnitWeights GeneralizedUniformServer.UnitWeights.Supplement
open GeneralizedUniformServer.Dev.WB
variable {k : ℕ} {M : Fin k → Type*}

end GeneralizedUniformServer.Dev.WB.PartM
end
end

section
set_option autoImplicit false
open scoped NNReal
noncomputable section
namespace GeneralizedUniformServer.Dev.WB.PartS
open GeneralizedUniformServer.UnitWeights GeneralizedUniformServer.UnitWeights.Supplement
open GeneralizedUniformServer.Dev.WB
variable {k : ℕ} {M : Fin k → Type*}
/-!
# Part S, core: couplings, chains, mixtures and sequential composition of strategies.
-/
/-! ## Linear structure of couplings -/
lemma fst_add (γ γ' : Cpl M) : (γ + γ').fst = γ.fst + γ'.fst := Finsupp.mapDomain_add

lemma snd_add (γ γ' : Cpl M) : (γ + γ').snd = γ.snd + γ'.snd := Finsupp.mapDomain_add

lemma fst_zero : (0 : Cpl M).fst = 0 := Finsupp.mapDomain_zero

lemma snd_zero : (0 : Cpl M).snd = 0 := Finsupp.mapDomain_zero

lemma fst_smul (c : ℝ≥0) (γ : Cpl M) : (c • γ).fst = c • γ.fst := Finsupp.mapDomain_smul _ _

lemma snd_smul (c : ℝ≥0) (γ : Cpl M) : (c • γ).snd = c • γ.snd := Finsupp.mapDomain_smul _ _

lemma fst_sum {α : Type*} (s : Finset α) (g : α → Cpl M) :
    (∑ a ∈ s, g a).fst = ∑ a ∈ s, (g a).fst := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [fst_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, fst_add, ih]

lemma snd_sum {α : Type*} (s : Finset α) (g : α → Cpl M) :
    (∑ a ∈ s, g a).snd = ∑ a ∈ s, (g a).snd := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [snd_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, snd_add, ih]

lemma fst_single (x y : Config M) (c : ℝ≥0) :
    Cpl.fst (Finsupp.single (x, y) c : Cpl M) = Finsupp.single x c := Finsupp.mapDomain_single

lemma snd_single (x y : Config M) (c : ℝ≥0) :
    Cpl.snd (Finsupp.single (x, y) c : Cpl M) = Finsupp.single y c := Finsupp.mapDomain_single

end GeneralizedUniformServer.Dev.WB.PartS
end
end

section
set_option autoImplicit false
open scoped NNReal
noncomputable section
namespace GeneralizedUniformServer.Dev.WB.PartS
open GeneralizedUniformServer.UnitWeights GeneralizedUniformServer.UnitWeights.Supplement
open GeneralizedUniformServer.Dev.WB
variable {k : ℕ} {M : Fin k → Type*}
variable (v : Fin k → ℝ≥0)
lemma cost_zero : Cpl.cost v (0 : Cpl M) = 0 := by simp [Cpl.cost]

lemma cost_add (γ γ' : Cpl M) : (γ + γ').cost v = γ.cost v + γ'.cost v := by
  unfold Cpl.cost
  exact Finsupp.sum_add_index' (fun _ => zero_mul _) (fun _ _ _ => add_mul _ _ _)

lemma cost_smul (c : ℝ≥0) (γ : Cpl M) : (c • γ).cost v = c * γ.cost v := by
  unfold Cpl.cost
  rw [Finsupp.sum_smul_index' (fun _ => zero_mul _), Finsupp.mul_sum]
  simp [smul_eq_mul, mul_assoc]

lemma cost_sum {α : Type*} (s : Finset α) (g : α → Cpl M) :
    (∑ a ∈ s, g a).cost v = ∑ a ∈ s, (g a).cost v := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [cost_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, cost_add, ih]

lemma cost_single (x y : Config M) (c : ℝ≥0) :
    Cpl.cost v (Finsupp.single (x, y) c : Cpl M) = c * wdist v x y := by
  unfold Cpl.cost
  rw [Finsupp.sum_single_index (zero_mul _)]

lemma wdist_self (x : Config M) : wdist v x x = 0 := by
  simp [wdist]

end GeneralizedUniformServer.Dev.WB.PartS
end
end

section
set_option autoImplicit false
open scoped NNReal
noncomputable section
namespace GeneralizedUniformServer.Dev.WB.PartS
open GeneralizedUniformServer.UnitWeights GeneralizedUniformServer.UnitWeights.Supplement
open GeneralizedUniformServer.Dev.WB
variable {k : ℕ} {M : Fin k → Type*}
lemma mass_fst (γ : Cpl M) : mass γ.fst = mass γ := by
  unfold mass Cpl.fst
  exact Finsupp.sum_mapDomain_index (fun _ => rfl) (fun _ _ _ => rfl)

lemma mass_snd (γ : Cpl M) : mass γ.snd = mass γ := by
  unfold mass Cpl.snd
  exact Finsupp.sum_mapDomain_index (fun _ => rfl) (fun _ _ _ => rfl)

lemma mass_single {α : Type*} (a : α) (c : ℝ≥0) : mass (Finsupp.single a c) = c := by
  unfold mass
  exact Finsupp.sum_single_index rfl

lemma mass_eq_sum {α : Type*} (μ : α →₀ ℝ≥0) : mass μ = ∑ y ∈ μ.support, μ y := rfl

lemma mem_support_snd {γ : Cpl M} {y : Config M} (h : y ∈ γ.snd.support) :
    ∃ xy ∈ γ.support, xy.2 = y := by
  classical
  have := Finsupp.mapDomain_support (f := Prod.snd) (s := γ) h
  simpa using this

lemma mem_support_sum_smul {α β : Type*} (s : Finset α) (c : α → ℝ≥0) (g : α → β →₀ ℝ≥0)
    {b : β} (h : b ∈ (∑ a ∈ s, c a • g a).support) : ∃ a ∈ s, b ∈ (g a).support := by
  classical
  have h1 := Finsupp.support_finsetSum (s := s) (f := fun a => c a • g a) h
  simp only [Finset.mem_biUnion] at h1
  obtain ⟨a, ha, hb⟩ := h1
  exact ⟨a, ha, Finsupp.support_smul hb⟩

lemma sum_smul_single_one {α : Type*} (ν : α →₀ ℝ≥0) :
    ∑ y ∈ ν.support, ν y • Finsupp.single y (1 : ℝ≥0) = ν := by
  conv_rhs => rw [← Finsupp.sum_single ν]
  unfold Finsupp.sum
  refine Finset.sum_congr rfl fun y _ => ?_
  simp

/-! ## Chains -/
/-- End law of a chain started at `μ` (the last second marginal, or `μ` if empty). -/
def endD : (Config M →₀ ℝ≥0) → List (Cpl M) → (Config M →₀ ℝ≥0)
  | μ, [] => μ
  | _, γ :: l => endD γ.snd l

@[simp] lemma endD_nil (μ : Config M →₀ ℝ≥0) : endD μ [] = μ := rfl

@[simp] lemma endD_cons (μ : Config M →₀ ℝ≥0) (γ : Cpl M) (l : List (Cpl M)) :
    endD μ (γ :: l) = endD γ.snd l := rfl

@[simp] lemma isChainD_nil (μ : Config M →₀ ℝ≥0) : IsChainD μ ([] : List (Cpl M)) := trivial

@[simp] lemma isChainD_cons (μ : Config M →₀ ℝ≥0) (γ : Cpl M) (l : List (Cpl M)) :
    IsChainD μ (γ :: l) ↔ γ.fst = μ ∧ IsChainD γ.snd l := Iff.rfl

lemma isChainD_append (μ : Config M →₀ ℝ≥0) (l₁ l₂ : List (Cpl M)) :
    IsChainD μ (l₁ ++ l₂) ↔ IsChainD μ l₁ ∧ IsChainD (endD μ l₁) l₂ := by
  induction l₁ generalizing μ with
  | nil => simp
  | cons γ l ih => simp [ih, and_assoc]

lemma mass_endD {μ : Config M →₀ ℝ≥0} {l : List (Cpl M)} (h : IsChainD μ l) :
    mass (endD μ l) = mass μ := by
  induction l generalizing μ with
  | nil => rfl
  | cons γ l ih =>
    rw [isChainD_cons] at h
    rw [endD_cons, ih h.2, mass_snd, ← mass_fst, h.1]

lemma mass_of_mem_chain {μ : Config M →₀ ℝ≥0} {l : List (Cpl M)} (h : IsChainD μ l)
    {γ : Cpl M} (hγ : γ ∈ l) : mass γ = mass μ := by
  induction l generalizing μ with
  | nil => simp at hγ
  | cons γ' l ih =>
    rw [isChainD_cons] at h
    rcases List.mem_cons.1 hγ with rfl | hγ
    · rw [← mass_fst, h.1]
    · rw [ih h.2 hγ, mass_snd, ← mass_fst, h.1]

lemma getD_cons_succ (γ : Cpl M) (l : List (Cpl M)) (t : ℕ) :
    (γ :: l).getD (t + 1) 0 = l.getD t 0 := by simp

lemma getD_cons_zero (γ : Cpl M) (l : List (Cpl M)) : (γ :: l).getD 0 0 = γ := by simp

lemma mem_support_endD {μ : Config M →₀ ℝ≥0} {l : List (Cpl M)} {y : Config M}
    (h : y ∈ (endD μ l).support) :
    y ∈ μ.support ∨ ∃ t, ∃ xy ∈ (l.getD t 0).support, xy.2 = y := by
  induction l generalizing μ with
  | nil => exact Or.inl h
  | cons γ l ih =>
    rcases ih h with h' | ⟨t, xy, hxy, hy⟩
    · obtain ⟨xy, hxy, hy⟩ := mem_support_snd h'
      exact Or.inr ⟨0, xy, by simpa using hxy, hy⟩
    · exact Or.inr ⟨t + 1, xy, by simpa using hxy, hy⟩

lemma chain_getD_zero {μ : Config M →₀ ℝ≥0} {l : List (Cpl M)} (h : IsChainD μ l)
    (hl : 0 < l.length) : (l.getD 0 0).fst = μ := by
  cases l with
  | nil => simp at hl
  | cons γ l => exact h.1

lemma chain_getD_succ {μ : Config M →₀ ℝ≥0} {l : List (Cpl M)} (h : IsChainD μ l)
    {t : ℕ} (ht : t + 1 < l.length) : (l.getD (t + 1) 0).fst = (l.getD t 0).snd := by
  induction l generalizing μ t with
  | nil => simp at ht
  | cons γ l ih =>
    rw [isChainD_cons] at h
    rw [getD_cons_succ]
    cases t with
    | zero =>
      rw [getD_cons_zero]
      exact chain_getD_zero h.2 (by simp at ht; omega)
    | succ t =>
      rw [getD_cons_succ]
      exact ih h.2 (by simp at ht; omega)

lemma isChainD_of_getD (μ : Config M →₀ ℝ≥0) (l : List (Cpl M))
    (h : ∀ t < l.length, (l.getD t 0).fst = if t = 0 then μ else (l.getD (t - 1) 0).snd) :
    IsChainD μ l := by
  induction l generalizing μ with
  | nil => trivial
  | cons γ l ih =>
    refine ⟨by simpa using h 0 (by simp), ih _ fun t ht => ?_⟩
    have := h (t + 1) (by simp; omega)
    rw [getD_cons_succ] at this
    rw [this]
    cases t with
    | zero => simp
    | succ t => simp

/-- Mass of every step of a chain started at a probability law. -/
lemma chain_mass_getD {μ : Config M →₀ ℝ≥0} {l : List (Cpl M)} (h : IsChainD μ l)
    {t : ℕ} (ht : t < l.length) : mass (l.getD t 0) = mass μ := by
  apply mass_of_mem_chain h
  rw [List.getD_eq_getElem _ _ ht]
  exact List.getElem_mem ht

end GeneralizedUniformServer.Dev.WB.PartS
end
end

section
set_option autoImplicit false
open scoped NNReal
noncomputable section
namespace GeneralizedUniformServer.Dev.WB.PartS
open GeneralizedUniformServer.UnitWeights GeneralizedUniformServer.UnitWeights.Supplement
open GeneralizedUniformServer.Dev.WB
variable {k : ℕ} {M : Fin k → Type*}
variable (v : Fin k → ℝ≥0)
/-! ## Chain cost -/
@[simp] lemma chainCost_nil : chainCost v ([] : List (Cpl M)) = 0 := rfl

@[simp] lemma chainCost_cons (γ : Cpl M) (l : List (Cpl M)) :
    chainCost v (γ :: l) = γ.cost v + chainCost v l := by
  simp [chainCost]

@[simp] lemma chainCost_append (l₁ l₂ : List (Cpl M)) :
    chainCost v (l₁ ++ l₂) = chainCost v l₁ + chainCost v l₂ := by
  simp [chainCost]

lemma chainCost_eq_sum (l : List (Cpl M)) :
    chainCost v l = ∑ t ∈ Finset.range l.length, (l.getD t 0).cost v := by
  induction l with
  | nil => simp
  | cons γ l ih =>
    rw [chainCost_cons, ih, List.length_cons, Finset.sum_range_succ']
    simp [add_comm]

lemma sum_range_cost_le (l : List (Cpl M)) (L : ℕ) :
    ∑ t ∈ Finset.range L, (l.getD t 0).cost v ≤ chainCost v l := by
  rw [chainCost_eq_sum]
  calc ∑ t ∈ Finset.range L, (l.getD t 0).cost v
      ≤ ∑ t ∈ Finset.range (max L l.length), (l.getD t 0).cost v :=
        Finset.sum_le_sum_of_subset (Finset.range_mono (le_max_left _ _))
    _ = ∑ t ∈ Finset.range l.length, (l.getD t 0).cost v := by
        symm
        apply Finset.sum_subset (Finset.range_mono (le_max_right _ _))
        intro t _ ht
        simp only [Finset.mem_range, not_lt] at ht
        rw [List.getD_eq_default _ _ ht, cost_zero]

end GeneralizedUniformServer.Dev.WB.PartS
end
end

section
set_option autoImplicit false
open scoped NNReal
noncomputable section
namespace GeneralizedUniformServer.Dev.WB.PartS
open GeneralizedUniformServer.UnitWeights GeneralizedUniformServer.UnitWeights.Supplement
open GeneralizedUniformServer.Dev.WB
variable {k : ℕ} {M : Fin k → Type*}
/-! ## Mixtures of strategies -/
/-- The mixture `∑_y ν y • g y`, step by step, over `L` steps. -/
def lmix (ν : Config M →₀ ℝ≥0) (g : Config M → List (Cpl M)) (L : ℕ) : List (Cpl M) :=
  List.ofFn fun t : Fin L => ∑ y ∈ ν.support, ν y • (g y).getD t 0

@[simp] lemma length_lmix (ν : Config M →₀ ℝ≥0) (g : Config M → List (Cpl M)) (L : ℕ) :
    (lmix ν g L).length = L := by simp [lmix]

lemma getD_lmix (ν : Config M →₀ ℝ≥0) (g : Config M → List (Cpl M)) (L : ℕ) {t : ℕ}
    (ht : t < L) : (lmix ν g L).getD t 0 = ∑ y ∈ ν.support, ν y • (g y).getD t 0 := by
  rw [List.getD_eq_getElem _ _ (by simpa using ht)]
  simp [lmix]

lemma getD_lmix_of_le (ν : Config M →₀ ℝ≥0) (g : Config M → List (Cpl M)) (L : ℕ) {t : ℕ}
    (ht : L ≤ t) : (lmix ν g L).getD t 0 = 0 :=
  List.getD_eq_default _ _ (by simpa using ht)

lemma getD_take (l : List (Cpl M)) {s t : ℕ} (h : t < s) :
    (l.take s).getD t 0 = l.getD t 0 := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_take, h, if_true]

lemma lmix_take (ν : Config M →₀ ℝ≥0) (g : Config M → List (Cpl M)) (L s : ℕ) :
    (lmix ν g L).take s = lmix ν (fun y => (g y).take s) (min L s) := by
  apply List.ext_getElem
  · simp [min_comm]
  · intro t h1 h2
    have ht1 : t < L := by simp at h2; omega
    have ht2 : t < s := by simp at h2; omega
    rw [List.getElem_take]
    have e1 := getD_lmix ν g L ht1
    have e2 := getD_lmix ν (fun y => (g y).take s) (min L s) (lt_min ht1 ht2)
    rw [List.getD_eq_getElem _ _ (by simpa using ht1)] at e1
    rw [List.getD_eq_getElem _ _ (by simp; omega)] at e2
    rw [e1, e2]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [getD_take _ ht2]

lemma isChainD_lmix (ν : Config M →₀ ℝ≥0) (g : Config M → List (Cpl M)) (L : ℕ)
    (h : ∀ y ∈ ν.support, IsChainD (Finsupp.single y 1) (g y) ∧ L ≤ (g y).length) :
    IsChainD ν (lmix ν g L) := by
  apply isChainD_of_getD
  intro t ht
  rw [length_lmix] at ht
  rw [getD_lmix _ _ _ ht, fst_sum]
  split_ifs with h0
  · subst h0
    conv_rhs => rw [← sum_smul_single_one ν]
    refine Finset.sum_congr rfl fun y hy => ?_
    rw [fst_smul, chain_getD_zero (h y hy).1 (by have := (h y hy).2; omega)]
  · rw [getD_lmix _ _ _ (by omega), snd_sum]
    refine Finset.sum_congr rfl fun y hy => ?_
    obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
    rw [fst_smul, snd_smul, chain_getD_succ (h y hy).1 (by have := (h y hy).2; omega)]
    simp

lemma mem_support_lmix {ν : Config M →₀ ℝ≥0} {g : Config M → List (Cpl M)} {L t : ℕ}
    {xy : Config M × Config M} (h : xy ∈ ((lmix ν g L).getD t 0).support) :
    ∃ y ∈ ν.support, xy ∈ ((g y).getD t 0).support := by
  by_cases ht : t < L
  · rw [getD_lmix _ _ _ ht] at h
    exact mem_support_sum_smul _ _ _ h
  · rw [getD_lmix_of_le _ _ _ (by omega)] at h
    simp at h

lemma chainCost_lmix_le (v : Fin k → ℝ≥0) (ν : Config M →₀ ℝ≥0)
    (g : Config M → List (Cpl M)) (L : ℕ) :
    chainCost v (lmix ν g L) ≤ ∑ y ∈ ν.support, ν y * chainCost v (g y) := by
  rw [chainCost_eq_sum, length_lmix]
  calc ∑ t ∈ Finset.range L, ((lmix ν g L).getD t 0).cost v
      = ∑ t ∈ Finset.range L, ∑ y ∈ ν.support, ν y * ((g y).getD t 0).cost v := by
        refine Finset.sum_congr rfl fun t ht => ?_
        rw [getD_lmix _ _ _ (Finset.mem_range.1 ht), cost_sum]
        simp [cost_smul]
    _ = ∑ y ∈ ν.support, ν y * ∑ t ∈ Finset.range L, ((g y).getD t 0).cost v := by
        rw [Finset.sum_comm]
        simp [Finset.mul_sum]
    _ ≤ ∑ y ∈ ν.support, ν y * chainCost v (g y) := by
        gcongr with y hy
        exact sum_range_cost_le v _ _

lemma real_sum_le_of_mass {ν : Config M →₀ ℝ≥0} (hν : mass ν = 1) (X : Config M → ℝ≥0)
    (B : ℝ) (hX : ∀ y ∈ ν.support, (X y : ℝ) ≤ B) :
    ((∑ y ∈ ν.support, ν y * X y : ℝ≥0) : ℝ) ≤ B := by
  have hm : (∑ y ∈ ν.support, (ν y : ℝ)) = 1 := by
    rw [mass_eq_sum] at hν
    exact_mod_cast hν
  push_cast
  calc ∑ y ∈ ν.support, (ν y : ℝ) * (X y : ℝ) ≤ ∑ y ∈ ν.support, (ν y : ℝ) * B :=
        Finset.sum_le_sum fun y hy => mul_le_mul_of_nonneg_left (hX y hy) (by positivity)
    _ = B := by rw [← Finset.sum_mul, hm, one_mul]

/-! ## Sequential composition -/
/-- Run `A` from `x`, then from its end law the mixture of the runs `g y` over `L` steps. -/
def seqR (x : Config M) (A : List (Cpl M)) (g : Config M → List (Cpl M)) (L : ℕ) :
    List (Cpl M) :=
  A ++ lmix (endD (Finsupp.single x 1) A) g L

@[simp] lemma length_seqR (x : Config M) (A : List (Cpl M)) (g : Config M → List (Cpl M))
    (L : ℕ) : (seqR x A g L).length = A.length + L := by simp [seqR]

lemma seqR_take (x : Config M) (A : List (Cpl M)) (g : Config M → List (Cpl M)) (L s : ℕ)
    (hs : A.length < s) :
    (seqR x A g L).take s = seqR x A (fun y => (g y).take (s - A.length)) (min L (s - A.length)) := by
  unfold seqR
  rw [List.take_append, List.take_of_length_le (by omega), lmix_take]

lemma seqR_take_le (x : Config M) (A : List (Cpl M)) (g : Config M → List (Cpl M)) (L s : ℕ)
    (hs : s ≤ A.length) : (seqR x A g L).take s = A.take s := by
  unfold seqR
  rw [List.take_append_of_le_length hs]

lemma isChainD_seqR (x : Config M) (A : List (Cpl M)) (g : Config M → List (Cpl M)) (L : ℕ)
    (hA : IsChainD (Finsupp.single x 1) A)
    (hg : ∀ y ∈ (endD (Finsupp.single x 1) A).support,
      IsChainD (Finsupp.single y 1) (g y) ∧ L ≤ (g y).length) :
    IsChainD (Finsupp.single x 1) (seqR x A g L) := by
  unfold seqR
  rw [isChainD_append]
  exact ⟨hA, isChainD_lmix _ _ _ hg⟩

lemma mem_support_seqR {x : Config M} {A : List (Cpl M)} {g : Config M → List (Cpl M)} {L t : ℕ}
    {xy : Config M × Config M} (h : xy ∈ ((seqR x A g L).getD t 0).support) :
    (t < A.length ∧ xy ∈ (A.getD t 0).support) ∨
      (A.length ≤ t ∧ ∃ y ∈ (endD (Finsupp.single x 1) A).support,
        xy ∈ ((g y).getD (t - A.length) 0).support) := by
  unfold seqR at h
  by_cases ht : t < A.length
  · left
    refine ⟨ht, ?_⟩
    rwa [List.getD_eq_getElem?_getD, List.getElem?_append_left ht,
      ← List.getD_eq_getElem?_getD] at h
  · right
    refine ⟨by omega, ?_⟩
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega),
      ← List.getD_eq_getElem?_getD] at h
    exact mem_support_lmix h

lemma chainCost_seqR_le (v : Fin k → ℝ≥0) (x : Config M) (A : List (Cpl M))
    (g : Config M → List (Cpl M)) (L : ℕ) (hA : IsChainD (Finsupp.single x 1) A) (B : ℝ)
    (hg : ∀ y ∈ (endD (Finsupp.single x 1) A).support, (chainCost v (g y) : ℝ) ≤ B) :
    (chainCost v (seqR x A g L) : ℝ) ≤ chainCost v A + B := by
  unfold seqR
  rw [chainCost_append, NNReal.coe_add]
  gcongr
  calc (chainCost v (lmix (endD (Finsupp.single x 1) A) g L) : ℝ)
      ≤ ((∑ y ∈ (endD (Finsupp.single x 1) A).support,
          (endD (Finsupp.single x 1) A) y * chainCost v (g y) : ℝ≥0) : ℝ) := by
        exact_mod_cast chainCost_lmix_le v _ g L
    _ ≤ B := real_sum_le_of_mass (by rw [mass_endD hA, mass_single]) _ B hg

/-- Points of the end law of a chain from `x`: `x` itself or a target of some step. -/
lemma mem_support_endD_single {x y : Config M} {A : List (Cpl M)}
    (h : y ∈ (endD (Finsupp.single x 1) A).support) :
    y = x ∨ ∃ t, ∃ xy ∈ (A.getD t 0).support, xy.2 = y := by
  rcases mem_support_endD h with h | h
  · left
    simpa [Finsupp.support_single] using h
  · exact Or.inr h

/-!
# Part S, parser: the phase parser is online and accepts at most the whole list.
-/
/-- Accepted length of a parse. -/
def acc (r : PR M) (ρ : List (Config M)) : ℕ := r.stop.getD ρ.length

/-- A parser that is online and stops inside the list. -/
structure PGood (f : List (Config M) → PR M) : Prop where
  le : ∀ ρ n, (f ρ).stop = some n → n ≤ ρ.length
  on1 : ∀ ρ t n, (f ρ).stop = some n → n < t → f (ρ.take t) = f ρ
  on2 : ∀ ρ t, 0 < t → (∀ n, (f ρ).stop = some n → t ≤ n) → (f (ρ.take t)).stop = none

/-- A parser that accepts its first request. -/
def PPos (f : List (Config M) → PR M) : Prop := ∀ ρ n, (f ρ).stop = some n → 1 ≤ n

lemma acc_of_none {r : PR M} {ρ : List (Config M)} (h : r.stop = none) : acc r ρ = ρ.length := by
  simp [acc, h]

lemma acc_of_some {r : PR M} {ρ : List (Config M)} {n : ℕ} (h : r.stop = some n) :
    acc r ρ = n := by
  simp [acc, h]

lemma PGood.acc_le {f : List (Config M) → PR M} (hf : PGood f) (ρ : List (Config M)) :
    acc (f ρ) ρ ≤ ρ.length := by
  cases h : (f ρ).stop with
  | none => rw [acc_of_none h]
  | some n => rw [acc_of_some h]; exact hf.le ρ n h

lemma PGood.acc_take {f : List (Config M) → PR M} (hf : PGood f) (ρ : List (Config M)) (t : ℕ) :
    acc (f (ρ.take t)) (ρ.take t) = min (acc (f ρ) ρ) t := by
  rcases Nat.eq_zero_or_pos t with rfl | ht
  · have := hf.acc_le (ρ.take 0)
    simp at this ⊢
    exact this
  cases h : (f ρ).stop with
  | none =>
    rw [acc_of_none h, acc_of_none (hf.on2 ρ t ht (by simp [h])), List.length_take, min_comm]
  | some n =>
    rw [acc_of_some h]
    by_cases hnt : n < t
    · rw [hf.on1 ρ t n h hnt, acc_of_some h]; omega
    · have hle := hf.le ρ n h
      rw [acc_of_none (hf.on2 ρ t ht (by simp [h]; omega)), List.length_take]
      omega

end GeneralizedUniformServer.Dev.WB.PartS
end
end

section
set_option autoImplicit false
open scoped NNReal
noncomputable section
namespace GeneralizedUniformServer.Dev.WB.PartS
open GeneralizedUniformServer.UnitWeights GeneralizedUniformServer.UnitWeights.Supplement
open GeneralizedUniformServer.Dev.WB
variable {k : ℕ} {M : Fin k → Type*}
variable (P : Config M → Prop)
/-! ## `scan` -/
lemma scan_lt {ρ : List (Config M)} {n : ℕ} (h : scan P ρ = some n) : n < ρ.length := by
  induction ρ generalizing n with
  | nil => simp [scan] at h
  | cons r ρ ih =>
    by_cases hr : P r
    · simp only [scan, hr, if_true, Option.map_eq_some_iff] at h
      obtain ⟨n', h', rfl⟩ := h
      have := ih h'
      simp; omega
    · simp only [scan, hr, if_false, Option.some.injEq] at h
      subst h; simp

lemma scan_take_some {ρ : List (Config M)} {n t : ℕ} (h : scan P ρ = some n) (ht : n < t) :
    scan P (ρ.take t) = some n := by
  induction ρ generalizing n t with
  | nil => simp [scan] at h
  | cons r ρ ih =>
    obtain ⟨t, rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
    by_cases hr : P r
    · simp only [scan, hr, if_true, Option.map_eq_some_iff] at h
      obtain ⟨n', h', rfl⟩ := h
      simp only [List.take_succ_cons, scan, hr, if_true, ih (t := t) h' (by omega), Option.map_some]
    · simp only [scan, hr, if_false, Option.some.injEq] at h
      simp [List.take_succ_cons, scan, hr, h]

lemma scan_take_none {ρ : List (Config M)} {t : ℕ} (h : ∀ n, scan P ρ = some n → t ≤ n) :
    scan P (ρ.take t) = none := by
  induction ρ generalizing t with
  | nil => simp [scan]
  | cons r ρ ih =>
    rcases t with _ | t
    · simp [scan]
    by_cases hr : P r
    · rw [List.take_succ_cons]
      simp only [scan, hr, if_true, Option.map_eq_none_iff]
      apply ih
      intro n hn
      have := h (n + 1) (by simp [scan, hr, hn])
      omega
    · have := h 0 (by simp [scan, hr])
      omega

lemma scan_prop {ρ : List (Config M)} {s : ℕ} (hs : s < (scan P ρ).getD ρ.length)
    (hsl : s < ρ.length) : P ρ[s] := by
  induction ρ generalizing s with
  | nil => simp at hsl
  | cons r ρ ih =>
    by_cases hr : P r
    · rcases s with _ | s
      · simpa using hr
      · simp only [List.getElem_cons_succ]
        apply ih _ (by simpa using hsl)
        simp only [scan, hr, if_true] at hs
        cases h : scan P ρ with
        | none => simp [h] at hs ⊢; omega
        | some n => simp [h] at hs ⊢; omega
    · simp [scan, hr] at hs

lemma scan_getD_take (ρ : List (Config M)) (t : ℕ) :
    (scan P (ρ.take t)).getD (ρ.take t).length = min ((scan P ρ).getD ρ.length) t := by
  cases h : scan P ρ with
  | none =>
    rw [scan_take_none P (by simp [h])]
    simp [min_comm]
  | some n =>
    have hn := scan_lt P h
    by_cases hnt : n < t
    · rw [scan_take_some P h hnt]; simp; omega
    · rw [scan_take_none P (by simp [h]; omega)]
      simp; omega

end GeneralizedUniformServer.Dev.WB.PartS
end
end

section
set_option autoImplicit false
open scoped NNReal
noncomputable section
namespace GeneralizedUniformServer.Dev.WB.PartS
open GeneralizedUniformServer.UnitWeights GeneralizedUniformServer.UnitWeights.Supplement
open GeneralizedUniformServer.Dev.WB
variable {k : ℕ} {M : Fin k → Type*}
variable [NeZero k] (U : PSet M)
/-! ## `phase0` -/
lemma phase0_cons_sat {r : Config M} (ρ : List (Config M)) (hr : Sat U r) :
    phase0 U (r :: ρ) = ⟨(phase0 U ρ).stop.map (· + 1), (phase0 U ρ).dem⟩ := by
  simp [phase0, hr]

lemma phase0_cons_not_none {r : Config M} (ρ : List (Config M)) (hr : ¬ Sat U r)
    (h : scan (Sat (Function.update U (srv 0) (some (r (srv 0))))) ρ = none) :
    phase0 U (r :: ρ) = ⟨none, 0⟩ := by
  simp [phase0, hr, h]

lemma phase0_cons_not_some {r : Config M} (ρ : List (Config M)) (hr : ¬ Sat U r) {n : ℕ}
    (h : scan (Sat (Function.update U (srv 0) (some (r (srv 0))))) ρ = some n) :
    phase0 U (r :: ρ) = ⟨some (n + 1), fun j => Finsupp.single (r j) 1⟩ := by
  simp [phase0, hr, h]

lemma acc_phase0_cons_not {r : Config M} (ρ : List (Config M)) (hr : ¬ Sat U r) :
    acc (phase0 U (r :: ρ)) (r :: ρ) =
      (scan (Sat (Function.update U (srv 0) (some (r (srv 0))))) ρ).getD ρ.length + 1 := by
  cases h : scan (Sat (Function.update U (srv 0) (some (r (srv 0))))) ρ with
  | none => rw [phase0_cons_not_none U ρ hr h]; simp [acc]
  | some n => rw [phase0_cons_not_some U ρ hr h]; simp [acc]

lemma acc_phase0_cons_sat {r : Config M} (ρ : List (Config M)) (hr : Sat U r) :
    acc (phase0 U (r :: ρ)) (r :: ρ) = acc (phase0 U ρ) ρ + 1 := by
  rw [phase0_cons_sat U ρ hr]
  cases h : (phase0 U ρ).stop <;> simp [acc, h]

lemma phase0_pgood : PGood (phase0 U) := by
  refine ⟨?_, ?_, ?_⟩
  · intro ρ
    induction ρ with
    | nil => intro n h; simp [phase0] at h
    | cons r ρ ih =>
      intro n h
      by_cases hr : Sat U r
      · rw [phase0_cons_sat U ρ hr] at h
        simp only [Option.map_eq_some_iff] at h
        obtain ⟨n', h', rfl⟩ := h
        have := ih n' h'
        simp; omega
      · cases hs : scan (Sat (Function.update U (srv 0) (some (r (srv 0))))) ρ with
        | none => rw [phase0_cons_not_none U ρ hr hs] at h; simp at h
        | some n' =>
          rw [phase0_cons_not_some U ρ hr hs] at h
          simp only [Option.some.injEq] at h
          have := scan_lt _ hs
          simp; omega
  · intro ρ
    induction ρ with
    | nil => intro t n h; simp [phase0] at h
    | cons r ρ ih =>
      intro t n h hnt
      obtain ⟨t, rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
      rw [List.take_succ_cons]
      by_cases hr : Sat U r
      · rw [phase0_cons_sat U ρ hr] at h
        simp only [Option.map_eq_some_iff] at h
        obtain ⟨n', h', rfl⟩ := h
        rw [phase0_cons_sat U _ hr, phase0_cons_sat U _ hr, ih t n' h' (by omega)]
      · cases hs : scan (Sat (Function.update U (srv 0) (some (r (srv 0))))) ρ with
        | none => rw [phase0_cons_not_none U ρ hr hs] at h; simp at h
        | some n' =>
          rw [phase0_cons_not_some U ρ hr hs] at h
          simp only [Option.some.injEq] at h
          rw [phase0_cons_not_some U _ hr hs, phase0_cons_not_some U _ hr (scan_take_some _ hs (by omega))]
  · intro ρ
    induction ρ with
    | nil => intro t _ _; simp [phase0]
    | cons r ρ ih =>
      intro t ht h
      obtain ⟨t, rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
      rw [List.take_succ_cons]
      by_cases hr : Sat U r
      · rw [phase0_cons_sat U _ hr]
        simp only [Option.map_eq_none_iff]
        rcases Nat.eq_zero_or_pos t with rfl | ht'
        · simp [phase0]
        apply ih t ht'
        intro n hn
        have := h (n + 1) (by rw [phase0_cons_sat U _ hr]; simp [hn])
        omega
      · cases hs : scan (Sat (Function.update U (srv 0) (some (r (srv 0))))) ρ with
        | none => rw [phase0_cons_not_none U _ hr (scan_take_none _ (by simp [hs]))]
        | some n' =>
          have := h (n' + 1) (by rw [phase0_cons_not_some U ρ hr hs])
          rw [phase0_cons_not_none U _ hr (scan_take_none _ (by simp [hs]; omega))]

lemma phase0_pos : PPos (phase0 U) := by
  intro ρ n h
  cases ρ with
  | nil => simp [phase0] at h
  | cons r ρ =>
    by_cases hr : Sat U r
    · rw [phase0_cons_sat U ρ hr] at h
      simp only [Option.map_eq_some_iff] at h
      obtain ⟨n', _, rfl⟩ := h
      omega
    · cases hs : scan (Sat (Function.update U (srv 0) (some (r (srv 0))))) ρ with
      | none => rw [phase0_cons_not_none U ρ hr hs] at h; simp at h
      | some n' =>
        rw [phase0_cons_not_some U ρ hr hs] at h
        simp only [Option.some.injEq] at h
        omega

end GeneralizedUniformServer.Dev.WB.PartS
end
end

section
set_option autoImplicit false
open scoped NNReal
noncomputable section
namespace GeneralizedUniformServer.Dev.WB.PartS
open GeneralizedUniformServer.UnitWeights GeneralizedUniformServer.UnitWeights.Supplement
open GeneralizedUniformServer.Dev.WB
variable {k : ℕ} {M : Fin k → Type*}
variable (f : List (Config M) → PR M)
/-! ## `iter` -/
lemma iter_zero (ρ : List (Config M)) : iter f 0 ρ = ⟨some 0, 0⟩ := by simp [iter]

lemma iter_succ_none (m : ℕ) {ρ : List (Config M)} (h : (f ρ).stop = none) :
    iter f (m + 1) ρ = ⟨none, 0⟩ := by simp [iter, h]

lemma iter_succ_some (m : ℕ) {ρ : List (Config M)} {n : ℕ} (h : (f ρ).stop = some n) :
    iter f (m + 1) ρ =
      ⟨(iter f m (ρ.drop n)).stop.map (n + ·), (f ρ).dem + (iter f m (ρ.drop n)).dem⟩ := by
  simp [iter, h]

lemma acc_iter_succ_some (hf : PGood f) (m : ℕ) {ρ : List (Config M)} {n : ℕ}
    (h : (f ρ).stop = some n) :
    acc (iter f (m + 1) ρ) ρ = n + acc (iter f m (ρ.drop n)) (ρ.drop n) := by
  have hn := hf.le ρ n h
  rw [iter_succ_some f m h]
  cases h' : (iter f m (ρ.drop n)).stop with
  | none => simp [acc, h']; omega
  | some n' => simp [acc, h']

lemma iter_pgood (hf : PGood f) (m : ℕ) : PGood (iter f m) := by
  induction m with
  | zero =>
    refine ⟨?_, ?_, ?_⟩
    · intro ρ n h; simp [iter_zero] at h; omega
    · intro ρ t n _ _; simp [iter_zero]
    · intro ρ t ht h
      have := h 0 (by simp [iter_zero])
      omega
  | succ m ih =>
    refine ⟨?_, ?_, ?_⟩
    · intro ρ N h
      cases hf' : (f ρ).stop with
      | none => rw [iter_succ_none f m hf'] at h; simp at h
      | some n =>
        rw [iter_succ_some f m hf'] at h
        simp only [Option.map_eq_some_iff] at h
        obtain ⟨n', h', rfl⟩ := h
        have h1 := ih.le _ n' h'
        have h2 := hf.le ρ n hf'
        simp at h1; omega
    · intro ρ t N h hNt
      cases hf' : (f ρ).stop with
      | none => rw [iter_succ_none f m hf'] at h; simp at h
      | some n =>
        rw [iter_succ_some f m hf'] at h
        simp only [Option.map_eq_some_iff] at h
        obtain ⟨n', h', rfl⟩ := h
        have e1 := hf.on1 ρ t n hf' (by omega)
        have hf2 : (f (ρ.take t)).stop = some n := by rw [e1, hf']
        rw [iter_succ_some f m hf2, iter_succ_some f m hf', e1, List.drop_take,
          ih.on1 _ _ n' h' (by omega)]
    · intro ρ t ht h
      cases hf' : (f ρ).stop with
      | none => rw [iter_succ_none f m (hf.on2 ρ t ht (by simp [hf']))]
      | some n =>
        by_cases hnt : n < t
        · have e1 := hf.on1 ρ t n hf' hnt
          have hf2 : (f (ρ.take t)).stop = some n := by rw [e1, hf']
          rw [iter_succ_some f m hf2, List.drop_take]
          simp only [Option.map_eq_none_iff]
          apply ih.on2 _ _ (by omega)
          intro n' hn'
          have := h (n + n') (by rw [iter_succ_some f m hf']; simp [hn'])
          omega
        · rw [iter_succ_none f m (hf.on2 ρ t ht (by simp [hf']; omega))]

lemma iter_pos (hf : PPos f) (m : ℕ) : PPos (iter f (m + 1)) := by
  intro ρ N h
  cases hf' : (f ρ).stop with
  | none => rw [iter_succ_none f m hf'] at h; simp at h
  | some n =>
    rw [iter_succ_some f m hf'] at h
    simp only [Option.map_eq_some_iff] at h
    obtain ⟨n', _, rfl⟩ := h
    have := hf ρ n hf'
    omega

end GeneralizedUniformServer.Dev.WB.PartS
end
end

section
set_option autoImplicit false
open scoped NNReal
noncomputable section
namespace GeneralizedUniformServer.Dev.WB.PartS
open GeneralizedUniformServer.UnitWeights GeneralizedUniformServer.UnitWeights.Supplement
open GeneralizedUniformServer.Dev.WB
variable {k : ℕ} {M : Fin k → Type*}
variable [NeZero k]
/-! ## The level step of the parser -/
/-- Server `i + 1` set to `p` in `U`. -/
def updU (U : PSet M) (i : ℕ) (p : M (srv (i + 1))) : PSet M :=
  Function.update U (srv (i + 1)) (some p)

/-- The critical set of the explore multiphase on `ρ`. -/
def critS (mi i : ℕ) (P : PSet M → List (Config M) → PR M) (U : PSet M)
    (ρ : List (Config M)) : Finset (M (srv (i + 1))) :=
  crit ((iter (P U) mi ρ).dem (srv (i + 1))) (D (i + 1) - 1)

/-- Accepted length of the exploit part (the max of the copies' accepted lengths). -/
def nEx (mi i : ℕ) (P : PSet M → List (Config M) → PR M) (U : PSet M)
    (ρ : List (Config M)) (e : ℕ) : ℕ :=
  (critS mi i P U ρ).sup fun p => acc (iter (P (updU U i p)) mi (ρ.drop e)) (ρ.drop e)

open Classical in
/-- The body of `phase m (i+1)`, with the level-`i` parser abstracted. -/
def stepPhase (mi i : ℕ) (P : PSet M → List (Config M) → PR M) (U : PSet M)
    (ρ : List (Config M)) : PR M :=
    match (iter (P U) mi ρ).stop with
    | none => ⟨none, 0⟩
    | some e =>
      if ∀ p ∈ crit ((iter (P U) mi ρ).dem (srv (i + 1))) (D (i + 1) - 1),
          (iter (P (Function.update U (srv (i + 1)) (some p))) mi (ρ.drop e)).stop ≠ none
      then
        ⟨some (e + (crit ((iter (P U) mi ρ).dem (srv (i + 1))) (D (i + 1) - 1)).sup
            fun p => ((iter (P (Function.update U (srv (i + 1)) (some p))) mi
              (ρ.drop e)).stop.getD 0)),
          (iter (P U) mi ρ).dem +
            ∑ p ∈ crit ((iter (P U) mi ρ).dem (srv (i + 1))) (D (i + 1) - 1),
              (iter (P (Function.update U (srv (i + 1)) (some p))) mi (ρ.drop e)).dem⟩
      else ⟨none, 0⟩

lemma phase_succ (m : ℕ → ℕ) (i : ℕ) (U : PSet M) (ρ : List (Config M)) :
    phase m (i + 1) U ρ = stepPhase (m i) i (phase m i) U ρ := rfl

end GeneralizedUniformServer.Dev.WB.PartS
end
end

section
set_option autoImplicit false
open scoped NNReal
noncomputable section
namespace GeneralizedUniformServer.Dev.WB.PartS
open GeneralizedUniformServer.UnitWeights GeneralizedUniformServer.UnitWeights.Supplement
open GeneralizedUniformServer.Dev.WB
variable {k : ℕ} {M : Fin k → Type*}
variable [NeZero k]
variable (mi i : ℕ) (P : PSet M → List (Config M) → PR M) (U : PSet M)
lemma stepPhase_none {ρ : List (Config M)} (h : (iter (P U) mi ρ).stop = none) :
    stepPhase mi i P U ρ = ⟨none, 0⟩ := by
  simp [stepPhase, h]

lemma stepPhase_pos {ρ : List (Config M)} {e : ℕ} (h : (iter (P U) mi ρ).stop = some e)
    (hall : ∀ p ∈ critS mi i P U ρ, (iter (P (updU U i p)) mi (ρ.drop e)).stop ≠ none) :
    stepPhase mi i P U ρ =
      ⟨some (e + (critS mi i P U ρ).sup fun p =>
          ((iter (P (updU U i p)) mi (ρ.drop e)).stop.getD 0)),
        (iter (P U) mi ρ).dem + ∑ p ∈ critS mi i P U ρ, (iter (P (updU U i p)) mi (ρ.drop e)).dem⟩ := by
  unfold critS updU at *
  simp only [stepPhase, h]
  rw [if_pos hall]

lemma stepPhase_neg {ρ : List (Config M)} {e : ℕ} (h : (iter (P U) mi ρ).stop = some e)
    (hex : ∃ p ∈ critS mi i P U ρ, (iter (P (updU U i p)) mi (ρ.drop e)).stop = none) :
    stepPhase mi i P U ρ = ⟨none, 0⟩ := by
  unfold critS updU at *
  simp only [stepPhase, h]
  rw [if_neg]
  push Not
  exact hex

end GeneralizedUniformServer.Dev.WB.PartS
end
end

section
set_option autoImplicit false
open scoped NNReal
noncomputable section
namespace GeneralizedUniformServer.Dev.WB.PartS
open GeneralizedUniformServer.UnitWeights GeneralizedUniformServer.UnitWeights.Supplement
open GeneralizedUniformServer.Dev.WB
variable {k : ℕ} {M : Fin k → Type*}
variable [NeZero k]
variable (mi i : ℕ) (P : PSet M → List (Config M) → PR M) (U : PSet M)
variable (hP : ∀ U, PGood (P U))
include hP
lemma acc_stepPhase_some {ρ : List (Config M)} {e : ℕ} (h : (iter (P U) mi ρ).stop = some e) :
    acc (stepPhase mi i P U ρ) ρ = e + nEx mi i P U ρ e := by
  have hIt := fun U => iter_pgood (P U) (hP U) mi
  have he := (hIt U).le ρ e h
  by_cases hall : ∀ p ∈ critS mi i P U ρ, (iter (P (updU U i p)) mi (ρ.drop e)).stop ≠ none
  · rw [stepPhase_pos mi i P U h hall, acc_of_some rfl, nEx]
    congr 1
    refine Finset.sup_congr rfl fun p hp => ?_
    obtain ⟨n, hn⟩ := Option.ne_none_iff_exists'.1 (hall p hp)
    rw [hn, acc_of_some hn]; rfl
  · push Not at hall
    obtain ⟨p, hp, hpn⟩ := hall
    rw [stepPhase_neg mi i P U h ⟨p, hp, hpn⟩, acc_of_none rfl]
    have h1 : nEx mi i P U ρ e ≤ ρ.length - e := by
      unfold nEx
      apply Finset.sup_le
      intro q _
      have := (hIt (updU U i q)).acc_le (ρ.drop e)
      simpa using this
    have h2 : ρ.length - e ≤ nEx mi i P U ρ e := by
      have := Finset.le_sup (f := fun p => acc (iter (P (updU U i p)) mi (ρ.drop e)) (ρ.drop e)) hp
      rw [acc_of_none hpn] at this
      simpa [nEx] using this
    omega

lemma stepPhase_pgood : PGood (stepPhase mi i P U) := by
  have hIt := fun U => iter_pgood (P U) (hP U) mi
  refine ⟨?_, ?_, ?_⟩
  · intro ρ N hN
    have := (show acc (stepPhase mi i P U ρ) ρ = N from acc_of_some hN)
    cases h : (iter (P U) mi ρ).stop with
    | none => rw [stepPhase_none mi i P U h] at hN; simp at hN
    | some e =>
      rw [acc_stepPhase_some mi i P U hP h] at this
      have he := (hIt U).le ρ e h
      have h1 : nEx mi i P U ρ e ≤ ρ.length - e := by
        unfold nEx
        apply Finset.sup_le
        intro q _
        have := (hIt (updU U i q)).acc_le (ρ.drop e)
        simpa using this
      omega
  · intro ρ t N hN hNt
    cases h : (iter (P U) mi ρ).stop with
    | none => rw [stepPhase_none mi i P U h] at hN; simp at hN
    | some e =>
      by_cases hall : ∀ p ∈ critS mi i P U ρ, (iter (P (updU U i p)) mi (ρ.drop e)).stop ≠ none
      · rw [stepPhase_pos mi i P U h hall] at hN ⊢
        simp only [Option.some.injEq] at hN
        have heN : e ≤ N := by omega
        have e1 := (hIt U).on1 ρ t e h (by omega)
        have hS : critS mi i P U (ρ.take t) = critS mi i P U ρ := by simp [critS, e1]
        have h2 : (iter (P U) mi (ρ.take t)).stop = some e := by rw [e1, h]
        have hcp : ∀ p ∈ critS mi i P U ρ,
            iter (P (updU U i p)) mi ((ρ.take t).drop e) = iter (P (updU U i p)) mi (ρ.drop e) := by
          intro p hp
          obtain ⟨n, hn⟩ := Option.ne_none_iff_exists'.1 (hall p hp)
          rw [List.drop_take]
          apply (hIt _).on1 _ _ n hn
          have : n ≤ (critS mi i P U ρ).sup fun p =>
              ((iter (P (updU U i p)) mi (ρ.drop e)).stop.getD 0) :=
            le_trans (by simp [hn]) (Finset.le_sup (f := fun p =>
              ((iter (P (updU U i p)) mi (ρ.drop e)).stop.getD 0)) hp)
          omega
        have hall' : ∀ p ∈ critS mi i P U (ρ.take t),
            (iter (P (updU U i p)) mi ((ρ.take t).drop e)).stop ≠ none := by
          rw [hS]; intro p hp; rw [hcp p hp]; exact hall p hp
        rw [stepPhase_pos mi i P U h2 hall', hS, e1]
        congr 2
        · congr 1
          exact Finset.sup_congr rfl fun p hp => by rw [hcp p hp]
        · exact Finset.sum_congr rfl fun p hp => by rw [hcp p hp]
      · push Not at hall
        rw [stepPhase_neg mi i P U h hall] at hN
        simp at hN
  · intro ρ t ht hN
    cases h : (iter (P U) mi ρ).stop with
    | none => rw [stepPhase_none mi i P U ((hIt U).on2 ρ t ht (by simp [h]))]
    | some e =>
      by_cases het : e < t
      · have e1 := (hIt U).on1 ρ t e h het
        have h2 : (iter (P U) mi (ρ.take t)).stop = some e := by rw [e1, h]
        have hS : critS mi i P U (ρ.take t) = critS mi i P U ρ := by simp [critS, e1]
        apply congrArg PR.stop (stepPhase_neg mi i P U h2 _) |>.trans rfl
        rw [hS, List.drop_take]
        by_cases hall : ∀ p ∈ critS mi i P U ρ, (iter (P (updU U i p)) mi (ρ.drop e)).stop ≠ none
        · have hN' := hN _ (by rw [stepPhase_pos mi i P U h hall])
          have hpos : (⊥ : ℕ) < t - e := by simp; omega
          have : t - e ≤ (critS mi i P U ρ).sup fun p =>
              ((iter (P (updU U i p)) mi (ρ.drop e)).stop.getD 0) := by omega
          obtain ⟨p, hp, hpt⟩ := (Finset.le_sup_iff hpos).1 this
          refine ⟨p, hp, (hIt _).on2 _ _ (by omega) ?_⟩
          intro n hn
          simp [hn] at hpt
          omega
        · push Not at hall
          obtain ⟨p, hp, hpn⟩ := hall
          exact ⟨p, hp, (hIt _).on2 _ _ (by omega) (by simp [hpn])⟩
      · rw [stepPhase_none mi i P U ((hIt U).on2 ρ t ht (by simp [h]; omega))]

end GeneralizedUniformServer.Dev.WB.PartS
end
end

section
set_option autoImplicit false
open scoped NNReal
noncomputable section
namespace GeneralizedUniformServer.Dev.WB.PartS
open GeneralizedUniformServer.UnitWeights GeneralizedUniformServer.UnitWeights.Supplement
open GeneralizedUniformServer.Dev.WB
variable {k : ℕ} {M : Fin k → Type*}
lemma stepPhase_pos' [NeZero k] (mi i : ℕ) (P : PSet M → List (Config M) → PR M) (U : PSet M)
    (hP : PPos (iter (P U) mi)) : PPos (stepPhase mi i P U) := by
  intro ρ N hN
  cases h : (iter (P U) mi ρ).stop with
  | none => rw [stepPhase_none mi i P U h] at hN; simp at hN
  | some e =>
    have := hP ρ e h
    by_cases hall : ∀ p ∈ critS mi i P U ρ, (iter (P (updU U i p)) mi (ρ.drop e)).stop ≠ none
    · rw [stepPhase_pos mi i P U h hall] at hN
      simp only [Option.some.injEq] at hN
      omega
    · push Not at hall
      rw [stepPhase_neg mi i P U h hall] at hN
      simp at hN

/-!
# Part S, the strategies: definitions, lengths and the online property.
-/
/-- A strategy family whose length is the accepted length of the parser and which is online. -/
structure RGood (f : List (Config M) → PR M) (R : Config M → List (Config M) → List (Cpl M)) :
    Prop where
  len : ∀ x ρ, (R x ρ).length = acc (f ρ) ρ
  online : ∀ x ρ t, R x (ρ.take t) = (R x ρ).take t

lemma eq_nil_of_len_le_zero {l : List (Cpl M)} (h : l.length ≤ 0) : l = [] :=
  List.eq_nil_of_length_eq_zero (by omega)

end GeneralizedUniformServer.Dev.WB.PartS
end
end

section
set_option autoImplicit false
open scoped NNReal
noncomputable section
namespace GeneralizedUniformServer.Dev.WB.PartS
open GeneralizedUniformServer.UnitWeights GeneralizedUniformServer.UnitWeights.Supplement
open GeneralizedUniformServer.Dev.WB
variable {k : ℕ} {M : Fin k → Type*}
variable [NeZero k]
/-! ## Level 0 -/
/-- The moved configuration of a level-0 phase. -/
def mv0 (x r : Config M) : Config M := Function.update x (srv 0) (r (srv 0))

/-- The number of requests accepted after the witness `r` of a level-0 phase. -/
def cnt0 (U : PSet M) (r : Config M) (ρ : List (Config M)) : ℕ :=
  (scan (Sat (Function.update U (srv 0) (some (r (srv 0))))) ρ).getD ρ.length

open Classical in
/-- The level-0 strategy: stay while `U` satisfies the requests, then move server `0` to the
witness's point and stay there. -/
def run0 (U : PSet M) : Config M → List (Config M) → List (Cpl M)
  | _, [] => []
  | x, r :: ρ =>
    if Sat U r then Finsupp.single (x, x) 1 :: run0 U x ρ
    else Finsupp.single (x, mv0 x r) 1 :: List.replicate (cnt0 U r ρ) (Finsupp.single (mv0 x r, mv0 x r) 1)

lemma run0_cons_sat (U : PSet M) (x r : Config M) (ρ : List (Config M)) (hr : Sat U r) :
    run0 U x (r :: ρ) = Finsupp.single (x, x) 1 :: run0 U x ρ := by
  simp [run0, hr]

lemma run0_cons_not (U : PSet M) (x r : Config M) (ρ : List (Config M)) (hr : ¬ Sat U r) :
    run0 U x (r :: ρ) = Finsupp.single (x, mv0 x r) 1 ::
      List.replicate (cnt0 U r ρ) (Finsupp.single (mv0 x r, mv0 x r) 1) := by
  simp [run0, hr]

lemma run0_rgood (U : PSet M) : RGood (phase0 U) (run0 U) := by
  have hlen : ∀ x ρ, (run0 U x ρ).length = acc (phase0 U ρ) ρ := by
    intro x ρ
    induction ρ with
    | nil => simp [run0, phase0, acc]
    | cons r ρ ih =>
      by_cases hr : Sat U r
      · rw [run0_cons_sat U x r ρ hr, acc_phase0_cons_sat U ρ hr, List.length_cons, ih]
      · rw [run0_cons_not U x r ρ hr, acc_phase0_cons_not U ρ hr]
        simp [cnt0]
  refine ⟨hlen, ?_⟩
  intro x ρ
  induction ρ with
  | nil => intro t; simp [run0]
  | cons r ρ ih =>
    intro t
    rcases t with _ | t
    · simp [run0]
    rw [List.take_succ_cons]
    by_cases hr : Sat U r
    · rw [run0_cons_sat U x r _ hr, run0_cons_sat U x r _ hr, ih, List.take_succ_cons]
    · rw [run0_cons_not U x r _ hr, run0_cons_not U x r _ hr, List.take_succ_cons,
        List.take_replicate]
      congr 2
      unfold cnt0
      rw [scan_getD_take, min_comm]

end GeneralizedUniformServer.Dev.WB.PartS
end
end

section
set_option autoImplicit false
open scoped NNReal
noncomputable section
namespace GeneralizedUniformServer.Dev.WB.PartS
open GeneralizedUniformServer.UnitWeights GeneralizedUniformServer.UnitWeights.Supplement
open GeneralizedUniformServer.Dev.WB
variable {k : ℕ} {M : Fin k → Type*}
/-! ## Multiphases -/
/-- `m` copies of the strategy `R` (for the parser `f`), one after the other; each starts from
the end law of the previous one. -/
def runIterF (f : List (Config M) → PR M) (R : Config M → List (Config M) → List (Cpl M)) :
    ℕ → Config M → List (Config M) → List (Cpl M)
  | 0, _, _ => []
  | m + 1, x, ρ =>
    match (f ρ).stop with
    | none => R x ρ
    | some n => seqR x (R x ρ) (fun y => runIterF f R m y (ρ.drop n))
        (acc (iter f m (ρ.drop n)) (ρ.drop n))

end GeneralizedUniformServer.Dev.WB.PartS
end
end

section
set_option autoImplicit false
open scoped NNReal
noncomputable section
namespace GeneralizedUniformServer.Dev.WB.PartS
open GeneralizedUniformServer.UnitWeights GeneralizedUniformServer.UnitWeights.Supplement
open GeneralizedUniformServer.Dev.WB
variable {k : ℕ} {M : Fin k → Type*}
variable (f : List (Config M) → PR M) (R : Config M → List (Config M) → List (Cpl M))
lemma runIterF_zero (x : Config M) (ρ : List (Config M)) : runIterF f R 0 x ρ = [] := rfl

lemma runIterF_succ_none (m : ℕ) (x : Config M) {ρ : List (Config M)} (h : (f ρ).stop = none) :
    runIterF f R (m + 1) x ρ = R x ρ := by
  simp [runIterF, h]

lemma runIterF_succ_some (m : ℕ) (x : Config M) {ρ : List (Config M)} {n : ℕ}
    (h : (f ρ).stop = some n) :
    runIterF f R (m + 1) x ρ = seqR x (R x ρ) (fun y => runIterF f R m y (ρ.drop n))
        (acc (iter f m (ρ.drop n)) (ρ.drop n)) := by
  simp [runIterF, h]

lemma runIterF_rgood (hf : PGood f) (hR : RGood f R) (m : ℕ) :
    RGood (iter f m) (runIterF f R m) := by
  induction m with
  | zero => exact ⟨fun x ρ => by simp [runIterF_zero, iter_zero, acc], fun x ρ t => by simp [runIterF_zero]⟩
  | succ m ih =>
    have hlen : ∀ x ρ, (runIterF f R (m + 1) x ρ).length = acc (iter f (m + 1) ρ) ρ := by
      intro x ρ
      cases h : (f ρ).stop with
      | none =>
        rw [runIterF_succ_none f R m x h, hR.len, acc_of_none h, acc_of_none]
        simp [iter_succ_none f m h]
      | some n =>
        rw [runIterF_succ_some f R m x h, acc_iter_succ_some f hf m h, length_seqR, hR.len,
          acc_of_some h]
    refine ⟨hlen, ?_⟩
    intro x ρ t
    rcases Nat.eq_zero_or_pos t with rfl | ht
    · rw [List.take_zero, List.take_zero]
      apply eq_nil_of_len_le_zero
      rw [hlen]
      simpa using (iter_pgood f hf (m + 1)).acc_le []
    cases h : (f ρ).stop with
    | none =>
      rw [runIterF_succ_none f R m x h, runIterF_succ_none f R m x (hf.on2 ρ t ht (by simp [h])),
        hR.online]
    | some n =>
      rw [runIterF_succ_some f R m x h]
      by_cases hnt : n < t
      · have e1 := hf.on1 ρ t n h hnt
        have h2 : (f (ρ.take t)).stop = some n := by rw [e1, h]
        have hA : (R x ρ).length = n := by rw [hR.len, acc_of_some h]
        rw [runIterF_succ_some f R m x h2, seqR_take _ _ _ _ _ (by omega), hR.online,
          List.take_of_length_le (by omega), hA, List.drop_take, (iter_pgood f hf m).acc_take]
        congr 1
        funext y
        rw [ih.online]
      · have hA : (R x ρ).length = n := by rw [hR.len, acc_of_some h]
        rw [runIterF_succ_none f R m x (hf.on2 ρ t ht (by simp [h]; omega)), hR.online,
          seqR_take_le _ _ _ _ _ (by omega)]

end GeneralizedUniformServer.Dev.WB.PartS
end
end

section
set_option autoImplicit false
open scoped NNReal
noncomputable section
namespace GeneralizedUniformServer.Dev.WB.PartS
open GeneralizedUniformServer.UnitWeights GeneralizedUniformServer.UnitWeights.Supplement
open GeneralizedUniformServer.Dev.WB
variable {k : ℕ} {M : Fin k → Type*}
variable [NeZero k] (v : Fin k → ℝ≥0)
/-! ## The level step -/
/-- The experts of the exploit part: one copy of the level-`i` multiphase per critical point. -/
def cpF (mi i : ℕ) (P : PSet M → List (Config M) → PR M)
    (Rn : PSet M → Config M → List (Config M) → List (Cpl M)) (U : PSet M)
    (ρ : List (Config M)) (e : ℕ) (y : Config M) (p : M (srv (i + 1))) : List (Cpl M) :=
  runIterF (P (updU U i p)) (Rn (updU U i p)) mi (Function.update y (srv (i + 1)) p) (ρ.drop e)

/-- The exploit part from `y`: the master over the copies. -/
def exF (mi i : ℕ) (P : PSet M → List (Config M) → PR M)
    (Rn : PSet M → Config M → List (Config M) → List (Cpl M)) (U : PSet M)
    (ρ : List (Config M)) (e : ℕ) (y : Config M) : List (Cpl M) :=
  master v (2 * v (srv (i + 1))) y (critS mi i P U ρ) (cpF mi i P Rn U ρ e y) (nEx mi i P U ρ e)

/-- The level-`(i+1)` phase strategy, with the level-`i` parser and strategies abstracted. -/
def stepRun (mi i : ℕ) (P : PSet M → List (Config M) → PR M)
    (Rn : PSet M → Config M → List (Config M) → List (Cpl M)) (U : PSet M) (x : Config M)
    (ρ : List (Config M)) : List (Cpl M) :=
  match (iter (P U) mi ρ).stop with
  | none => runIterF (P U) (Rn U) mi x ρ
  | some e => seqR x (runIterF (P U) (Rn U) mi x ρ) (exF v mi i P Rn U ρ e) (nEx mi i P U ρ e)

end GeneralizedUniformServer.Dev.WB.PartS
end
end

section
set_option autoImplicit false
open scoped NNReal
noncomputable section
namespace GeneralizedUniformServer.Dev.WB.PartS
open GeneralizedUniformServer.UnitWeights GeneralizedUniformServer.UnitWeights.Supplement
open GeneralizedUniformServer.Dev.WB
variable {k : ℕ} {M : Fin k → Type*}
variable [NeZero k] (v : Fin k → ℝ≥0)
variable (mi i : ℕ) (P : PSet M → List (Config M) → PR M)
    (Rn : PSet M → Config M → List (Config M) → List (Cpl M)) (U : PSet M)
lemma stepRun_none (x : Config M) {ρ : List (Config M)} (h : (iter (P U) mi ρ).stop = none) :
    stepRun v mi i P Rn U x ρ = runIterF (P U) (Rn U) mi x ρ := by
  simp [stepRun, h]

lemma stepRun_some (x : Config M) {ρ : List (Config M)} {e : ℕ}
    (h : (iter (P U) mi ρ).stop = some e) :
    stepRun v mi i P Rn U x ρ =
      seqR x (runIterF (P U) (Rn U) mi x ρ) (exF v mi i P Rn U ρ e) (nEx mi i P U ρ e) := by
  simp [stepRun, h]

lemma length_exF (ρ : List (Config M)) (e : ℕ) (y : Config M) :
    (exF v mi i P Rn U ρ e y).length = nEx mi i P U ρ e := by
  simp [exF, master]

lemma stepRun_rgood (hP : ∀ U, PGood (P U)) (hR : ∀ U, RGood (P U) (Rn U)) :
    RGood (stepPhase mi i P U) (stepRun v mi i P Rn U) := by
  have hIt := fun U => iter_pgood (P U) (hP U) mi
  have hRI := fun U => runIterF_rgood (P U) (Rn U) (hP U) (hR U) mi
  have hlen : ∀ x ρ, (stepRun v mi i P Rn U x ρ).length = acc (stepPhase mi i P U ρ) ρ := by
    intro x ρ
    cases h : (iter (P U) mi ρ).stop with
    | none =>
      rw [stepRun_none v mi i P Rn U x h, (hRI U).len, acc_of_none h,
        stepPhase_none mi i P U h, acc_of_none rfl]
    | some e =>
      rw [stepRun_some v mi i P Rn U x h, length_seqR, (hRI U).len, acc_of_some h,
        acc_stepPhase_some mi i P U hP h]
  refine ⟨hlen, ?_⟩
  intro x ρ t
  rcases Nat.eq_zero_or_pos t with rfl | ht
  · rw [List.take_zero, List.take_zero]
    apply eq_nil_of_len_le_zero
    rw [hlen]
    simpa using (stepPhase_pgood mi i P U hP).acc_le []
  cases h : (iter (P U) mi ρ).stop with
  | none =>
    rw [stepRun_none v mi i P Rn U x h, stepRun_none v mi i P Rn U x
      ((hIt U).on2 ρ t ht (by simp [h])), (hRI U).online]
  | some e =>
    rw [stepRun_some v mi i P Rn U x h]
    have hA : (runIterF (P U) (Rn U) mi x ρ).length = e := by rw [(hRI U).len, acc_of_some h]
    by_cases het : e < t
    · have e1 := (hIt U).on1 ρ t e h het
      have h2 : (iter (P U) mi (ρ.take t)).stop = some e := by rw [e1, h]
      have hS : critS mi i P U (ρ.take t) = critS mi i P U ρ := by simp [critS, e1]
      have hN : nEx mi i P U (ρ.take t) e = min (nEx mi i P U ρ e) (t - e) := by
        unfold nEx
        rw [hS]
        simp only [List.drop_take, (hIt _).acc_take]
        exact (Finset.sup_inf_distrib_right _ _ _).symm
      rw [stepRun_some v mi i P Rn U x h2, seqR_take _ _ _ _ _ (by omega), (hRI U).online,
        List.take_of_length_le (by omega), hA, hN]
      congr 1
      funext y
      unfold exF
      rw [master_take, hS, hN]
      congr 1
      funext p
      unfold cpF
      rw [List.drop_take, (hRI _).online]
    · rw [stepRun_none v mi i P Rn U x ((hIt U).on2 ρ t ht (by simp [h]; omega)), (hRI U).online,
        seqR_take_le _ _ _ _ _ (by omega)]

end GeneralizedUniformServer.Dev.WB.PartS
end
end

section
set_option autoImplicit false
open scoped NNReal
noncomputable section
namespace GeneralizedUniformServer.Dev.WB.PartS
open GeneralizedUniformServer.UnitWeights GeneralizedUniformServer.UnitWeights.Supplement
open GeneralizedUniformServer.Dev.WB
variable {k : ℕ} {M : Fin k → Type*}
/-! ## The strategies of all levels -/
/-- The `(i+1, U)`-phase strategy (level index `i`) from the configuration `x`. -/
def run [NeZero k] (v : Fin k → ℝ≥0) (m : ℕ → ℕ) :
    ℕ → PSet M → Config M → List (Config M) → List (Cpl M)
  | 0 => run0
  | i + 1 => stepRun v (m i) i (phase m i) (run v m i)

lemma run_zero [NeZero k] (v : Fin k → ℝ≥0) (m : ℕ → ℕ) : run v m 0 = (run0 : PSet M → _) := rfl

lemma run_succ [NeZero k] (v : Fin k → ℝ≥0) (m : ℕ → ℕ) (i : ℕ) :
    run v m (i + 1) = (stepRun v (m i) i (phase m i) (run v m i) : PSet M → _) := rfl

lemma phase_pgood [NeZero k] (m : ℕ → ℕ) (i : ℕ) (U : PSet M) : PGood (phase m i U) := by
  induction i generalizing U with
  | zero => exact phase0_pgood U
  | succ i ih =>
    have : phase m (i + 1) U = stepPhase (m i) i (phase m i) U := funext fun ρ => phase_succ m i U ρ
    rw [this]
    exact stepPhase_pgood (m i) i (phase m i) U ih

lemma run_rgood [NeZero k] (v : Fin k → ℝ≥0) (m : ℕ → ℕ) (i : ℕ) (U : PSet M) :
    RGood (phase m i U) (run v m i U) := by
  induction i generalizing U with
  | zero => exact run0_rgood U
  | succ i ih =>
    have : phase m (i + 1) U = stepPhase (m i) i (phase m i) U := funext fun ρ => phase_succ m i U ρ
    rw [this, run_succ]
    exact stepRun_rgood v (m i) i (phase m i) (run v m i) U (phase_pgood m i) ih

/-!
# Part S, semantics: the strategies are chains, serve the requests and have bounded cost
(Lemma 5.4).
-/
/-- A strategy family at level index `i` for the set `U`: from every `x` covering `U` it is a
chain from `x`, its configurations serve the requests and agree with `x` on servers `> i`,
and its cost is at most `C`. -/
structure SGood (v : Fin k → ℝ≥0) (i : ℕ) (U : PSet M)
    (R : Config M → List (Config M) → List (Cpl M)) (C : ℝ) : Prop where
  chain : ∀ x ρ, Covers x U → IsChainD (Finsupp.single x 1) (R x ρ)
  supp : ∀ x ρ, Covers x U → ∀ t xy, xy ∈ ((R x ρ).getD t 0).support →
    (∀ r, ρ[t]? = some r → Serves xy.2 r) ∧ ∀ j : Fin k, i < j.val → xy.2 j = x j
  cost : ∀ x ρ, Covers x U → (chainCost v (R x ρ) : ℝ) ≤ C

lemma SGood.mono {v : Fin k → ℝ≥0} {i : ℕ} {U : PSet M}
    {R : Config M → List (Config M) → List (Cpl M)} {C C' : ℝ} (h : SGood v i U R C)
    (hC : C ≤ C') : SGood v i U R C' :=
  ⟨h.chain, h.supp, fun x ρ hx => (h.cost x ρ hx).trans hC⟩

lemma covers_of_agree {i : ℕ} {U : PSet M} {x y : Config M} (hx : Covers x U)
    (hy : ∀ j : Fin k, i < j.val → y j = x j) (hU : ∀ j : Fin k, j.val ≤ i → U j = none) :
    Covers y U := by
  intro j u hj
  have : i < j.val := by
    by_contra h
    rw [hU j (by omega)] at hj
    exact absurd hj (by simp)
  rw [hy j this, hx j u hj]

lemma agree_endD {i : ℕ} {x y : Config M} {A : List (Cpl M)}
    (hA : ∀ t xy, xy ∈ (A.getD t 0).support → ∀ j : Fin k, i < j.val → xy.2 j = x j)
    (hy : y ∈ (endD (Finsupp.single x 1) A).support) : ∀ j : Fin k, i < j.val → y j = x j := by
  rcases mem_support_endD_single hy with rfl | ⟨t, xy, hxy, rfl⟩
  · exact fun _ _ => rfl
  · exact hA t xy hxy

lemma getD_ne_of_mem_support {l : List (Cpl M)} {t : ℕ} {xy : Config M × Config M}
    (h : xy ∈ (l.getD t 0).support) : t < l.length := by
  by_contra h'
  rw [List.getD_eq_default _ _ (by omega)] at h
  simp at h

/-! ## Multiphases -/
lemma runIterF_sgood (v : Fin k → ℝ≥0) (f : List (Config M) → PR M)
    (R : Config M → List (Config M) → List (Cpl M)) (hf : PGood f) (hR : RGood f R) (i : ℕ)
    (U : PSet M) (hU : ∀ j : Fin k, j.val ≤ i → U j = none) (C : ℝ) (hC : 0 ≤ C)
    (hS : SGood v i U R C) (m : ℕ) : SGood v i U (runIterF f R m) (m * C) := by
  induction m with
  | zero =>
    refine ⟨fun _ _ _ => trivial, fun x ρ _ t xy h => ?_, fun _ _ _ => by simp [runIterF_zero]⟩
    simp [runIterF_zero] at h
  | succ m ih =>
    have hRI := runIterF_rgood f R hf hR m
    refine ⟨?_, ?_, ?_⟩
    · intro x ρ hx
      cases h : (f ρ).stop with
      | none => rw [runIterF_succ_none f R m x h]; exact hS.chain x ρ hx
      | some n =>
        rw [runIterF_succ_some f R m x h]
        refine isChainD_seqR _ _ _ _ (hS.chain x ρ hx) fun y hy => ?_
        have hyx := agree_endD (fun t xy hxy => (hS.supp x ρ hx t xy hxy).2) hy
        exact ⟨ih.chain y _ (covers_of_agree hx hyx hU), by rw [hRI.len]⟩
    · intro x ρ hx t xy hxy
      cases h : (f ρ).stop with
      | none => rw [runIterF_succ_none f R m x h] at hxy; exact hS.supp x ρ hx t xy hxy
      | some n =>
        rw [runIterF_succ_some f R m x h] at hxy
        have hA : (R x ρ).length = n := by rw [hR.len, acc_of_some h]
        rcases mem_support_seqR hxy with ⟨_, h1⟩ | ⟨hle, y, hy, h1⟩
        · exact hS.supp x ρ hx t xy h1
        · have hyx := agree_endD (fun t xy hxy => (hS.supp x ρ hx t xy hxy).2) hy
          have := ih.supp y (ρ.drop n) (covers_of_agree hx hyx hU) _ xy h1
          refine ⟨fun r hr => this.1 r ?_, fun j hj => (this.2 j hj).trans (hyx j hj)⟩
          rw [List.getElem?_drop, hA, Nat.add_sub_cancel' (by omega)]
          exact hr
    · intro x ρ hx
      cases h : (f ρ).stop with
      | none =>
        rw [runIterF_succ_none f R m x h]
        refine (hS.cost x ρ hx).trans ?_
        push_cast
        nlinarith
      | some n =>
        rw [runIterF_succ_some f R m x h]
        refine (chainCost_seqR_le v _ _ _ _ (hS.chain x ρ hx) (m * C) fun y hy => ?_).trans ?_
        · have hyx := agree_endD (fun t xy hxy => (hS.supp x ρ hx t xy hxy).2) hy
          exact ih.cost y _ (covers_of_agree hx hyx hU)
        · have := hS.cost x ρ hx
          push_cast
          linarith

/-! ## Level 0 -/
lemma wdist_update_le (v : Fin k → ℝ≥0) (x : Config M) (j : Fin k) (c : M j) :
    wdist v x (Function.update x j c) ≤ v j := by
  unfold wdist
  rw [Finset.sum_eq_single j]
  · split_ifs <;> simp
  · intro b _ hb
    rw [Function.update_of_ne hb]
    simp
  · simp

lemma srv_val [NeZero k] {i : ℕ} (hi : i < k) : (srv i : Fin k).val = i := Nat.mod_eq_of_lt hi

lemma chainCost_replicate_zero (v : Fin k → ℝ≥0) (n : ℕ) (γ : Cpl M) (hγ : γ.cost v = 0) :
    chainCost v (List.replicate n γ) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [List.replicate_succ, chainCost_cons, ih, hγ, add_zero]

lemma isChainD_replicate (z : Config M) (n : ℕ) :
    IsChainD (Finsupp.single z 1) (List.replicate n (Finsupp.single (z, z) 1 : Cpl M)) := by
  induction n with
  | zero => trivial
  | succ n ih => exact ⟨fst_single _ _ _, by rw [snd_single]; exact ih⟩

lemma run0_sgood [NeZero k] (v : Fin k → ℝ≥0) (U : PSet M) :
    SGood v 0 U (run0 U) (v (srv 0)) := by
  have h0 : (srv 0 : Fin k).val = 0 := srv_val (NeZero.pos k)
  refine ⟨?_, ?_, ?_⟩
  · intro x ρ _
    induction ρ with
    | nil => trivial
    | cons r ρ ih =>
      by_cases hr : Sat U r
      · rw [run0_cons_sat U x r ρ hr]
        exact ⟨fst_single _ _ _, by rw [snd_single]; exact ih⟩
      · rw [run0_cons_not U x r ρ hr]
        exact ⟨fst_single _ _ _, by rw [snd_single]; exact isChainD_replicate _ _⟩
  · intro x ρ hx
    induction ρ with
    | nil => intro t xy h; simp [run0] at h
    | cons r ρ ih =>
      intro t xy h
      by_cases hr : Sat U r
      · rw [run0_cons_sat U x r ρ hr] at h
        rcases t with _ | t
        · simp only [getD_cons_zero, Finsupp.support_single_ne_zero _ one_ne_zero,
            Finset.mem_singleton] at h
          subst h
          refine ⟨fun r' hr' => ?_, fun _ _ => rfl⟩
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hr'
          subst hr'
          obtain ⟨j, hj⟩ := hr
          exact ⟨j, hx j _ hj⟩
        · rw [getD_cons_succ] at h
          exact ih t xy h
      · rw [run0_cons_not U x r ρ hr] at h
        rcases t with _ | t
        · simp only [getD_cons_zero, Finsupp.support_single_ne_zero _ one_ne_zero,
            Finset.mem_singleton] at h
          subst h
          refine ⟨fun r' hr' => ?_, fun j hj => ?_⟩
          · simp only [List.getElem?_cons_zero, Option.some.injEq] at hr'
            subst hr'
            exact ⟨srv 0, by simp [mv0]⟩
          · have : j ≠ srv 0 := fun h => by rw [h, h0] at hj; omega
            simp [mv0, Function.update_of_ne this]
        · rw [getD_cons_succ] at h
          have hlt := getD_ne_of_mem_support h
          rw [List.length_replicate] at hlt
          rw [List.getD_eq_getElem _ _ (by simpa using hlt), List.getElem_replicate,
            Finsupp.support_single_ne_zero _ one_ne_zero, Finset.mem_singleton] at h
          subst h
          refine ⟨fun r' hr' => ?_, fun j hj => ?_⟩
          · simp only [List.getElem?_cons_succ] at hr'
            obtain ⟨hs, rfl⟩ := List.getElem?_eq_some_iff.1 hr'
            obtain ⟨j, hj⟩ := scan_prop _ hlt hs
            by_cases hj0 : j = srv 0
            · subst hj0
              simp only [Function.update_self, Option.some.injEq] at hj
              exact ⟨srv 0, by simp [mv0, hj]⟩
            · rw [Function.update_of_ne hj0] at hj
              refine ⟨j, ?_⟩
              simp [mv0, Function.update_of_ne hj0, hx j _ hj]
          · have : j ≠ srv 0 := fun h => by rw [h, h0] at hj; omega
            simp [mv0, Function.update_of_ne this]
  · intro x ρ _
    induction ρ with
    | nil => simp [run0]
    | cons r ρ ih =>
      by_cases hr : Sat U r
      · rw [run0_cons_sat U x r ρ hr, chainCost_cons, cost_single, wdist_self]
        simpa using ih
      · rw [run0_cons_not U x r ρ hr, chainCost_cons, cost_single,
          chainCost_replicate_zero v _ _ (by rw [cost_single, wdist_self, mul_zero])]
        simpa [mv0] using wdist_update_le v x (srv 0) (r (srv 0))

/-! ## Critical sets -/
lemma crit_card_le {α : Type*} (V : α →₀ ℕ) (n : ℕ) : (crit V n).card ≤ n := by
  classical
  induction n with
  | zero => simp [crit]
  | succ n ih =>
    rw [crit]
    split
    · exact (Finset.card_insert_le _ _).trans (by omega)
    · omega

lemma crit_nonempty {α : Type*} [Nonempty α] (V : α →₀ ℕ) (n : ℕ) (hn : 0 < n) :
    (crit V n).Nonempty := by
  classical
  induction n with
  | zero => omega
  | succ n ih =>
    rw [crit]
    split
    · exact Finset.insert_nonempty _ _
    · rename_i h
      rcases Nat.eq_zero_or_pos n with rfl | hn'
      · exfalso
        apply h
        simp only [crit, Finset.notMem_empty, not_false_eq_true, forall_const, true_and]
        by_cases hV : V.support.Nonempty
        · obtain ⟨q, _, hq⟩ := Finset.exists_max_image V.support V hV
          refine ⟨q, fun q' => ?_⟩
          by_cases hq' : q' ∈ V.support
          · exact hq q' hq'
          · rw [Finsupp.notMem_support_iff.1 hq']; omega
        · obtain ⟨q⟩ := ‹Nonempty α›
          refine ⟨q, fun q' => ?_⟩
          rw [Finsupp.notMem_support_iff.1 (fun h' => hV ⟨q', h'⟩)]
          omega
      · exact ih hn'

end GeneralizedUniformServer.Dev.WB.PartS
end
end

section
set_option autoImplicit false
open scoped NNReal
noncomputable section
namespace GeneralizedUniformServer.Dev.WB.PartS
open GeneralizedUniformServer.UnitWeights GeneralizedUniformServer.UnitWeights.Supplement
open GeneralizedUniformServer.Dev.WB
variable {k : ℕ} {M : Fin k → Type*}
variable [NeZero k] (v : Fin k → ℝ≥0) (mi i : ℕ) (P : PSet M → List (Config M) → PR M)
    (Rn : PSet M → Config M → List (Config M) → List (Cpl M))
/-!
# Part S, the level step (Lemma 5.4): explore multiphase, then the master over the copies.
-/
lemma ne_srv {i : ℕ} (hi : i < k) {j : Fin k} (hj : j.val ≠ i) : j ≠ srv i :=
  fun h => hj (by rw [h, srv_val hi])

lemma updU_none (hi : i + 1 < k) (U : PSet M) (hU : ∀ j : Fin k, j.val ≤ i + 1 → U j = none)
    (p : M (srv (i + 1))) : ∀ j : Fin k, j.val ≤ i → updU U i p j = none := by
  intro j hj
  rw [updU, Function.update_of_ne (ne_srv hi (by omega)), hU j (by omega)]

lemma covers_updU (U : PSet M) (y : Config M) (hy : Covers y U) (p : M (srv (i + 1))) :
    Covers (Function.update y (srv (i + 1)) p) (updU U i p) := by
  intro j u hj
  by_cases h : j = srv (i + 1)
  · subst h
    simp only [updU, Function.update_self, Option.some.injEq] at hj
    simp [hj]
  · rw [updU, Function.update_of_ne h] at hj
    rw [Function.update_of_ne h]
    exact hy j u hj

lemma two_le_D (i : ℕ) : 2 ≤ D (i + 1) := by
  unfold D
  have h5 : 5 ≤ 5 ^ (i + 1) := by
    calc 5 = 5 ^ 1 := by norm_num
      _ ≤ 5 ^ (i + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  calc 2 = 2 ^ 1 := by norm_num
    _ ≤ 2 ^ (5 ^ (i + 1) - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)

lemma length_cpF (hP : ∀ U, PGood (P U)) (hR : ∀ U, RGood (P U) (Rn U)) (U : PSet M)
    (ρ : List (Config M)) (e : ℕ) (y : Config M) (p : M (srv (i + 1))) :
    (cpF mi i P Rn U ρ e y p).length = acc (iter (P (updU U i p)) mi (ρ.drop e)) (ρ.drop e) :=
  (runIterF_rgood _ _ (hP _) (hR _) mi).len _ _

end GeneralizedUniformServer.Dev.WB.PartS
end
end

section
set_option autoImplicit false
open scoped NNReal
noncomputable section
namespace GeneralizedUniformServer.Dev.WB.PartS
open GeneralizedUniformServer.UnitWeights GeneralizedUniformServer.UnitWeights.Supplement
open GeneralizedUniformServer.Dev.WB
variable {k : ℕ} {M : Fin k → Type*}
variable [NeZero k] (v : Fin k → ℝ≥0) (mi i : ℕ) (P : PSet M → List (Config M) → PR M)
    (Rn : PSet M → Config M → List (Config M) → List (Cpl M))
variable (hi : i + 1 < k) (hpos : 0 < v (srv (i + 1)))
    (hdiam : ∀ z z' : Config M, (∀ j : Fin k, i + 1 < j.val → z j = z' j) →
      wdist v z z' ≤ 2 * v (srv (i + 1)))
    (hP : ∀ U, PGood (P U)) (hR : ∀ U, RGood (P U) (Rn U))
include hi hpos hdiam hP hR in
lemma exF_hyp (C : ℝ)
    (hS : ∀ U' : PSet M, (∀ j : Fin k, j.val ≤ i → U' j = none) →
      SGood v i U' (runIterF (P U') (Rn U') mi) C)
    (U : PSet M) (hU : ∀ j : Fin k, j.val ≤ i + 1 → U j = none) (y : Config M) (hy : Covers y U)
    (ρ : List (Config M)) (e : ℕ) :
    MasterHyp v (2 * v (srv (i + 1))) y (critS mi i P U ρ) (cpF mi i P Rn U ρ e y)
      (nEx mi i P U ρ e) (fun p => Function.update y (srv (i + 1)) p)
      {z | ∀ j : Fin k, i + 1 < j.val → z j = y j} := by
  have hne : (critS mi i P U ρ).Nonempty := by
    have : Nonempty (M (srv (i + 1))) := ⟨y _⟩
    exact crit_nonempty _ _ (by have := two_le_D i; omega)
  refine ⟨by positivity, fun z hz z' hz' => hdiam z z' fun j hj => (hz j hj).trans (hz' j hj).symm,
    fun j _ => rfl, hne, fun p _ => (hS _ (updU_none i hi U hU p)).chain _ _ (covers_updU i U y hy p),
    fun p _ j hj => by simp [Function.update_of_ne (ne_srv hi (j := j) (by omega))], ?_, ?_, ?_⟩
  · intro p _ γ hγ xy hxy j hj
    obtain ⟨t, ht, rfl⟩ := List.mem_iff_getElem.1 hγ
    have := ((hS _ (updU_none i hi U hU p)).supp _ (ρ.drop e) (covers_updU i U y hy p) t xy
      (by show xy ∈ ((cpF mi i P Rn U ρ e y p).getD t 0).support
          rwa [List.getD_eq_getElem _ _ ht])).2 j (by omega)
    rw [this, Function.update_of_ne (ne_srv hi (by omega))]
  · intro p hp
    rw [length_cpF mi i P Rn hP hR]
    exact Finset.le_sup (f := fun p => acc (iter (P (updU U i p)) mi (ρ.drop e)) (ρ.drop e)) hp
  · right
    obtain ⟨p, hp, hmax⟩ := Finset.exists_mem_eq_sup _ hne
      (fun p => acc (iter (P (updU U i p)) mi (ρ.drop e)) (ρ.drop e))
    exact ⟨p, hp, by rw [length_cpF mi i P Rn hP hR, nEx, hmax]⟩

include hi hpos hdiam hP hR in
lemma stepRun_sgood (C : ℝ) (hC : 0 ≤ C)
    (hS0 : ∀ U' : PSet M, (∀ j : Fin k, j.val ≤ i → U' j = none) → SGood v i U' (Rn U') C)
    (U : PSet M) (hU : ∀ j : Fin k, j.val ≤ i + 1 → U j = none) :
    SGood v (i + 1) U (stepRun v mi i P Rn U)
      (mi * C + (2 * (v (srv (i + 1)) : ℝ) + 2 * (2 * (v (srv (i + 1)) : ℝ)) *
        Real.log (D (i + 1)) + 2 * (mi * C))) := by
  have hS : ∀ U' : PSet M, (∀ j : Fin k, j.val ≤ i → U' j = none) →
      SGood v i U' (runIterF (P U') (Rn U') mi) (mi * C) := fun U' hU' =>
    runIterF_sgood v _ _ (hP U') (hR U') i U' hU' C hC (hS0 U' hU') mi
  have hUi : ∀ j : Fin k, j.val ≤ i → U j = none := fun j hj => hU j (by omega)
  have hA := hS U hUi
  have hlog0 : 0 ≤ Real.log (D (i + 1)) := Real.log_nonneg (by
    have := two_le_D i
    exact_mod_cast (show 1 ≤ D (i + 1) by omega))
  refine ⟨?_, ?_, ?_⟩
  · intro x ρ hx
    cases h : (iter (P U) mi ρ).stop with
    | none => rw [stepRun_none v mi i P Rn U x h]; exact hA.chain x ρ hx
    | some e =>
      rw [stepRun_some v mi i P Rn U x h]
      refine isChainD_seqR _ _ _ _ (hA.chain x ρ hx) fun y hy => ?_
      have hyx := agree_endD (fun t xy hxy => (hA.supp x ρ hx t xy hxy).2) hy
      have hyU := covers_of_agree hx hyx hUi
      exact ⟨master_chain v _ y _ _ _ _ _
        (exF_hyp v mi i P Rn hi hpos hdiam hP hR _ hS U hU y hyU ρ e),
        by rw [length_exF]⟩
  · intro x ρ hx t xy hxy
    cases h : (iter (P U) mi ρ).stop with
    | none =>
      rw [stepRun_none v mi i P Rn U x h] at hxy
      have := hA.supp x ρ hx t xy hxy
      exact ⟨this.1, fun j hj => this.2 j (by omega)⟩
    | some e =>
      rw [stepRun_some v mi i P Rn U x h] at hxy
      have hAl : (runIterF (P U) (Rn U) mi x ρ).length = e := by
        rw [(runIterF_rgood _ _ (hP U) (hR U) mi).len, acc_of_some h]
      rcases mem_support_seqR hxy with ⟨_, h1⟩ | ⟨hle, y, hy, h1⟩
      · have := hA.supp x ρ hx t xy h1
        exact ⟨this.1, fun j hj => this.2 j (by omega)⟩
      · have hyx := agree_endD (fun t xy hxy => (hA.supp x ρ hx t xy hxy).2) hy
        have hyU := covers_of_agree hx hyx hUi
        have hlt := getD_ne_of_mem_support h1
        rw [length_exF] at hlt
        obtain ⟨p, hp, _, xy', hxy', heq⟩ := master_supp v _ y _ _ _ _ _
          (exF_hyp v mi i P Rn hi hpos hdiam hP hR _ hS U hU y hyU ρ e) _ hlt xy h1
        have := (hS _ (updU_none i hi U hU p)).supp _ _ (covers_updU i U y hyU p) _ xy' hxy'
        refine ⟨fun r hr => ?_, fun j hj => ?_⟩
        · rw [← heq]
          apply this.1 r
          rw [List.getElem?_drop, hAl, Nat.add_sub_cancel' (by omega)]
          exact hr
        · rw [← heq, this.2 j (by omega), Function.update_of_ne (ne_srv hi (by omega)),
            hyx j (by omega)]
  · intro x ρ hx
    have hAc := hA.cost x ρ hx
    have hv0 : (0 : ℝ) ≤ v (srv (i + 1)) := by positivity
    have hmi : (0 : ℝ) ≤ mi * C := by positivity
    cases h : (iter (P U) mi ρ).stop with
    | none =>
      rw [stepRun_none v mi i P Rn U x h]
      have : 0 ≤ 2 * (v (srv (i + 1)) : ℝ) * Real.log (D (i + 1)) := by positivity
      nlinarith
    | some e =>
      rw [stepRun_some v mi i P Rn U x h]
      refine (chainCost_seqR_le v _ _ _ _ (hA.chain x ρ hx)
        (2 * (v (srv (i + 1)) : ℝ) + 2 * (2 * (v (srv (i + 1)) : ℝ)) *
          Real.log (D (i + 1)) + 2 * (mi * C)) fun y hy => ?_).trans (by linarith)
      have hyx := agree_endD (fun t xy hxy => (hA.supp x ρ hx t xy hxy).2) hy
      have hyU := covers_of_agree hx hyx hUi
      have hyp := exF_hyp v mi i P Rn hi hpos hdiam hP hR _ hS U hU y hyU ρ e
      have hne : (critS mi i P U ρ).Nonempty := hyp.nonempty
      obtain ⟨p, hp, hmax⟩ := Finset.exists_mem_eq_sup _ hne
        (fun p => acc (iter (P (updU U i p)) mi (ρ.drop e)) (ρ.drop e))
      have hpl : (cpF mi i P Rn U ρ e y p).length = nEx mi i P U ρ e := by
        rw [length_cpF mi i P Rn hP hR, nEx, hmax]
      have hmc := master_cost v _ y _ _ _ _ _ hyp p hp hpl
      have hcp : (chainCost v (cpF mi i P Rn U ρ e y p) : ℝ) ≤ mi * C :=
        (hS _ (updU_none i hi U hU p)).cost _ (ρ.drop e) (covers_updU i U y hyU p)
      have hcard : Real.log (critS mi i P U ρ).card ≤ Real.log (D (i + 1)) := by
        apply Real.log_le_log (by exact_mod_cast hne.card_pos)
        have := crit_card_le ((iter (P U) mi ρ).dem (srv (i + 1))) (D (i + 1) - 1)
        exact_mod_cast (show (critS mi i P U ρ).card ≤ D (i + 1) by unfold critS; omega)
      have h4 : 2 * (2 * (v (srv (i + 1)) : ℝ)) * Real.log (critS mi i P U ρ).card ≤
          2 * (2 * (v (srv (i + 1)) : ℝ)) * Real.log (D (i + 1)) :=
        mul_le_mul_of_nonneg_left hcard (by positivity)
      unfold exF
      push_cast at hmc
      linarith

end GeneralizedUniformServer.Dev.WB.PartS
end
end

section
set_option autoImplicit false
open scoped NNReal
noncomputable section
namespace GeneralizedUniformServer.Dev.WB.PartS
open GeneralizedUniformServer.UnitWeights GeneralizedUniformServer.UnitWeights.Supplement
open GeneralizedUniformServer.Dev.WB
variable {k : ℕ} {M : Fin k → Type*}
variable [NeZero k] (v : Fin k → ℝ≥0) (m : ℕ → ℕ) (hv : Normalized v m)
include hv
/-!
# Part S, all levels: the `(i+1, U)`-phase strategy costs at most `10 · 5^i · v_i`.
-/
lemma sum_le_two : ∀ (l : ℕ) (hl : l < k),
    ∑ j : Fin k, (if j.val ≤ l then v j else 0) ≤ 2 * v ⟨l, hl⟩ := by
  intro l
  induction l with
  | zero =>
    intro hl
    rw [Finset.sum_eq_single ⟨0, hl⟩]
    · simp only [le_refl, if_true]
      rw [two_mul]; exact le_add_self
    · intro b _ hb
      rw [if_neg]
      intro h
      exact hb (Fin.ext (by show b.val = 0; omega))
    · simp
  | succ l ih =>
    intro hl
    have hsplit : ∀ j : Fin k, (if j.val ≤ l + 1 then v j else 0) =
        (if j.val ≤ l then v j else 0) + (if j = ⟨l + 1, hl⟩ then v j else 0) := by
      intro j
      by_cases h1 : j.val ≤ l
      · have : j ≠ ⟨l + 1, hl⟩ := fun h => by rw [h] at h1; simp at h1
        simp [h1, this, show j.val ≤ l + 1 by omega]
      · by_cases h2 : j.val = l + 1
        · have : j = ⟨l + 1, hl⟩ := Fin.ext h2
          simp [this]
        · have : j ≠ ⟨l + 1, hl⟩ := fun h => h2 (by rw [h])
          simp [h1, this, show ¬ j.val ≤ l + 1 by omega]
    rw [Finset.sum_congr rfl fun j _ => hsplit j, Finset.sum_add_distrib, Finset.sum_ite_eq']
    simp only [Finset.mem_univ, if_true]
    have h1 := ih (by omega)
    have h2 := (hv.2 l hl).2
    have h3 := (hv.2 l hl).1
    have : 2 * v ⟨l, by omega⟩ ≤ v ⟨l + 1, hl⟩ := by
      rw [h2]
      gcongr
      exact_mod_cast h3
    calc _ ≤ 2 * v ⟨l, by omega⟩ + v ⟨l + 1, hl⟩ := by gcongr
      _ ≤ v ⟨l + 1, hl⟩ + v ⟨l + 1, hl⟩ := by gcongr
      _ = 2 * v ⟨l + 1, hl⟩ := by rw [two_mul]

lemma diam_le (i : ℕ) (hi : i + 1 < k) (z z' : Config M)
    (h : ∀ j : Fin k, i + 1 < j.val → z j = z' j) : wdist v z z' ≤ 2 * v (srv (i + 1)) := by
  have hs : srv (i + 1) = (⟨i + 1, hi⟩ : Fin k) := Fin.ext (srv_val hi)
  rw [hs]
  refine le_trans ?_ (sum_le_two v m hv (i + 1) hi)
  unfold wdist
  refine Finset.sum_le_sum fun j _ => ?_
  split_ifs with h1 h2 h2
  · exact le_refl _
  · exact absurd (h j (by omega)) h1
  · positivity
  · exact le_refl _

omit hv in
lemma log_D_le (i : ℕ) : Real.log (D (i + 1) : ℝ) ≤ 3.5 * 5 ^ i := by
  have hD : ((D (i + 1) : ℕ) : ℝ) = (2 : ℝ) ^ (5 ^ (i + 1) - 1) := by
    simp [D]
  rw [hD, Real.log_pow]
  have h1 : ((5 ^ (i + 1) - 1 : ℕ) : ℝ) ≤ 5 * 5 ^ i := by
    have : 5 ^ (i + 1) - 1 ≤ 5 ^ (i + 1) := Nat.sub_le _ _
    have : ((5 ^ (i + 1) - 1 : ℕ) : ℝ) ≤ ((5 ^ (i + 1) : ℕ) : ℝ) := by exact_mod_cast this
    simpa [pow_succ, mul_comm] using this
  have h2 := Real.log_two_lt_d9
  have h3 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have h4 : (0 : ℝ) ≤ 5 ^ i := by positivity
  have h5 : (0 : ℝ) ≤ ((5 ^ (i + 1) - 1 : ℕ) : ℝ) := by positivity
  calc ((5 ^ (i + 1) - 1 : ℕ) : ℝ) * Real.log 2 ≤ (5 * 5 ^ i) * 0.7 := by
        apply mul_le_mul h1 (by linarith) h3 (by positivity)
    _ = 3.5 * 5 ^ i := by ring

lemma level_sgood (i : ℕ) (hi : i < k) (U : PSet M) (hU : ∀ j : Fin k, j.val ≤ i → U j = none) :
    SGood v i U (run v m i U) (10 * 5 ^ i * v (srv i)) := by
  induction i generalizing U with
  | zero =>
    rw [run_zero]
    refine (run0_sgood v U).mono ?_
    have : (0 : ℝ) ≤ v (srv 0) := by positivity
    simp only [pow_zero, mul_one]
    linarith
  | succ i ih =>
    have hs1 : srv (i + 1) = (⟨i + 1, hi⟩ : Fin k) := Fin.ext (srv_val hi)
    have hs0 : srv i = (⟨i, by omega⟩ : Fin k) := Fin.ext (srv_val (by omega))
    have hrel : (v (srv (i + 1)) : ℝ) = m i * v (srv i) := by
      rw [hs1, hs0, (hv.2 i hi).2]; push_cast; ring
    rw [run_succ]
    refine (stepRun_sgood v (m i) i (phase m i) (run v m i) hi (hv.1 _)
      (diam_le v m hv i hi) (phase_pgood m i) (run_rgood v m i) _ (by positivity)
      (fun U' hU' => ih (by omega) U' hU') U hU).mono ?_
    have hlog := log_D_le i
    set V : ℝ := (v (srv (i + 1)) : ℝ) with hV
    have hV0 : 0 ≤ V := by positivity
    have hp : (1 : ℝ) ≤ 5 ^ i := one_le_pow₀ (by norm_num)
    have e1 : (m i : ℝ) * (10 * 5 ^ i * v (srv i)) = 10 * 5 ^ i * V := by rw [hrel]; ring
    rw [e1, pow_succ]
    have h1 : V * Real.log (D (i + 1)) ≤ V * (3.5 * 5 ^ i) := mul_le_mul_of_nonneg_left hlog hV0
    have h2 : V ≤ V * 5 ^ i := le_mul_of_one_le_right hV0 hp
    nlinarith

lemma phase_pos (i : ℕ) (hi : i < k) (U : PSet M) : PPos (phase m i U) := by
  induction i generalizing U with
  | zero => exact phase0_pos U
  | succ i ih =>
    have : phase m (i + 1) U = stepPhase (m i) i (phase m i) U := funext fun ρ => phase_succ m i U ρ
    rw [this]
    apply stepPhase_pos'
    obtain ⟨n, hn⟩ : ∃ n, m i = n + 1 := ⟨m i - 1, by have := (hv.2 i hi).1; omega⟩
    rw [hn]
    exact iter_pos _ (ih (by omega) U) n

end GeneralizedUniformServer.Dev.WB.PartS
end
end

section
set_option autoImplicit false
open scoped NNReal
noncomputable section
namespace GeneralizedUniformServer.Dev.WB.PartS
open GeneralizedUniformServer.UnitWeights GeneralizedUniformServer.UnitWeights.Supplement
open GeneralizedUniformServer.Dev.WB
variable {k : ℕ} {M : Fin k → Type*}
variable (P : List (Config M) → PR M) (R : Config M → List (Config M) → List (Cpl M))
/-!
# Part S, the global strategy: consecutive top-level phases (§5.5 "The algorithm").
-/
/-- Consecutive phases of the parser `P`, each run with `R` from the end law of the previous
one (`fuel` bounds the recursion, as in `ncallsAux`). -/
def globAux : ℕ → Config M → List (Config M) → List (Cpl M)
  | 0, _, _ => []
  | _ + 1, _, [] => []
  | fuel + 1, x, r :: ρ =>
    match (P (r :: ρ)).stop with
    | none => R x (r :: ρ)
    | some n => seqR x (R x (r :: ρ)) (fun y => globAux fuel y ((r :: ρ).drop n))
        ((r :: ρ).length - n)

lemma globAux_nil (fuel : ℕ) (x : Config M) : globAux P R fuel x [] = [] := by
  cases fuel <;> rfl

lemma globAux_none (fuel : ℕ) (x : Config M) {ρ : List (Config M)} (hρ : ρ ≠ [])
    (h : (P ρ).stop = none) : globAux P R (fuel + 1) x ρ = R x ρ := by
  obtain ⟨r, ρ, rfl⟩ := List.exists_cons_of_ne_nil hρ
  simp [globAux, h]

lemma globAux_some (fuel : ℕ) (x : Config M) {ρ : List (Config M)} (hρ : ρ ≠ []) {n : ℕ}
    (h : (P ρ).stop = some n) : globAux P R (fuel + 1) x ρ =
      seqR x (R x ρ) (fun y => globAux P R fuel y (ρ.drop n)) (ρ.length - n) := by
  obtain ⟨r, ρ, rfl⟩ := List.exists_cons_of_ne_nil hρ
  simp [globAux, h]

lemma ncallsAux_none (fuel : ℕ) {ρ : List (Config M)} (hρ : ρ ≠ [])
    (h : (P ρ).stop = none) : ncallsAux P (fuel + 1) ρ = 1 := by
  obtain ⟨r, ρ, rfl⟩ := List.exists_cons_of_ne_nil hρ
  simp [ncallsAux, h]

lemma ncallsAux_some (fuel : ℕ) {ρ : List (Config M)} (hρ : ρ ≠ []) {n : ℕ}
    (h : (P ρ).stop = some n) : ncallsAux P (fuel + 1) ρ = 1 + ncallsAux P fuel (ρ.drop n) := by
  obtain ⟨r, ρ, rfl⟩ := List.exists_cons_of_ne_nil hρ
  simp [ncallsAux, h]

end GeneralizedUniformServer.Dev.WB.PartS
end
end

section
set_option autoImplicit false
open scoped NNReal
noncomputable section
namespace GeneralizedUniformServer.Dev.WB.PartS
open GeneralizedUniformServer.UnitWeights GeneralizedUniformServer.UnitWeights.Supplement
open GeneralizedUniformServer.Dev.WB
variable {k : ℕ} {M : Fin k → Type*}
variable (P : List (Config M) → PR M) (R : Config M → List (Config M) → List (Cpl M))
variable (hP : PGood P) (hpos : PPos P) (hR : RGood P R)
include hP hpos hR
lemma globAux_length : ∀ (fuel : ℕ) (x : Config M) (ρ : List (Config M)), ρ.length ≤ fuel →
    (globAux P R fuel x ρ).length = ρ.length := by
  intro fuel
  induction fuel with
  | zero => intro x ρ h; simp at h; subst h; rfl
  | succ fuel ih =>
    intro x ρ hl
    rcases eq_or_ne ρ [] with rfl | hρ
    · rfl
    cases h : (P ρ).stop with
    | none => rw [globAux_none P R fuel x hρ h, hR.len, acc_of_none h]
    | some n =>
      have h1 := hpos ρ n h
      have h2 := hP.le ρ n h
      rw [globAux_some P R fuel x hρ h, length_seqR, hR.len, acc_of_some h]
      omega

omit hP hR in
lemma globAux_fuel : ∀ (f₁ f₂ : ℕ) (x : Config M) (ρ : List (Config M)), ρ.length ≤ f₁ →
    ρ.length ≤ f₂ → globAux P R f₁ x ρ = globAux P R f₂ x ρ := by
  intro f₁
  induction f₁ with
  | zero =>
    intro f₂ x ρ h _
    simp at h; subst h
    rw [globAux_nil, globAux_nil]
  | succ f₁ ih =>
    intro f₂ x ρ h1 h2
    rcases eq_or_ne ρ [] with rfl | hρ
    · rw [globAux_nil, globAux_nil]
    obtain ⟨f₂, rfl⟩ : ∃ f, f₂ = f + 1 := ⟨f₂ - 1, by
      have := List.length_pos_of_ne_nil hρ; omega⟩
    cases h : (P ρ).stop with
    | none => rw [globAux_none P R _ x hρ h, globAux_none P R _ x hρ h]
    | some n =>
      have hn := hpos ρ n h
      rw [globAux_some P R _ x hρ h, globAux_some P R _ x hρ h]
      congr 1
      funext y
      exact ih f₂ y _ (by simp; omega) (by simp; omega)

omit hpos in
lemma globAux_online : ∀ (fuel : ℕ) (x : Config M) (ρ : List (Config M)) (t : ℕ),
    globAux P R fuel x (ρ.take t) = (globAux P R fuel x ρ).take t := by
  intro fuel
  induction fuel with
  | zero => intro x ρ t; simp [globAux]
  | succ fuel ih =>
    intro x ρ t
    rcases eq_or_ne ρ [] with rfl | hρ
    · simp [globAux_nil]
    rcases Nat.eq_zero_or_pos t with rfl | ht
    · simp [globAux_nil]
    have hρt : ρ.take t ≠ [] := by
      simp only [ne_eq, List.take_eq_nil_iff, not_or]; exact ⟨by omega, hρ⟩
    cases h : (P ρ).stop with
    | none =>
      rw [globAux_none P R fuel x hρ h, globAux_none P R fuel x hρt (hP.on2 ρ t ht (by simp [h])),
        hR.online]
    | some n =>
      have hA : (R x ρ).length = n := by rw [hR.len, acc_of_some h]
      rw [globAux_some P R fuel x hρ h]
      by_cases hnt : n < t
      · have e1 := hP.on1 ρ t n h hnt
        have h2 : (P (ρ.take t)).stop = some n := by rw [e1, h]
        rw [globAux_some P R fuel x hρt h2, seqR_take _ _ _ _ _ (by omega), hR.online,
          List.take_of_length_le (by omega), hA, List.drop_take]
        congr 1
        · funext y
          rw [ih]
        · simp; omega
      · rw [globAux_none P R fuel x hρt (hP.on2 ρ t ht (by simp [h]; omega)), hR.online,
          seqR_take_le _ _ _ _ _ (by omega)]

end GeneralizedUniformServer.Dev.WB.PartS
end
end

section
set_option autoImplicit false
open scoped NNReal
noncomputable section
namespace GeneralizedUniformServer.Dev.WB.PartS
open GeneralizedUniformServer.UnitWeights GeneralizedUniformServer.UnitWeights.Supplement
open GeneralizedUniformServer.Dev.WB
variable {k : ℕ} {M : Fin k → Type*}
variable (P : List (Config M) → PR M) (R : Config M → List (Config M) → List (Cpl M))
variable (hP : PGood P) (hpos : PPos P) (hR : RGood P R)
include hP hpos hR
variable (v : Fin k → ℝ≥0) (i : ℕ) (U : PSet M) (C : ℝ) (hS : SGood v i U R C)
    (hcov : ∀ x : Config M, Covers x U)
include hS hcov
lemma globAux_chain : ∀ (fuel : ℕ) (x : Config M) (ρ : List (Config M)), ρ.length ≤ fuel →
    IsChainD (Finsupp.single x 1) (globAux P R fuel x ρ) := by
  intro fuel
  induction fuel with
  | zero => intro x ρ _; trivial
  | succ fuel ih =>
    intro x ρ hl
    rcases eq_or_ne ρ [] with rfl | hρ
    · rw [globAux_nil]; trivial
    cases h : (P ρ).stop with
    | none => rw [globAux_none P R fuel x hρ h]; exact hS.chain x ρ (hcov x)
    | some n =>
      have hn := hpos ρ n h
      rw [globAux_some P R fuel x hρ h]
      refine isChainD_seqR _ _ _ _ (hS.chain x ρ (hcov x)) fun y _ =>
        ⟨ih y _ (by simp; omega), ?_⟩
      rw [globAux_length P R hP hpos hR _ _ _ (by simp; omega)]
      simp

omit hP hpos in
lemma globAux_serves : ∀ (fuel : ℕ) (x : Config M) (ρ : List (Config M)) (t : ℕ)
    (xy : Config M × Config M), xy ∈ ((globAux P R fuel x ρ).getD t 0).support →
    ∀ r, ρ[t]? = some r → Serves xy.2 r := by
  intro fuel
  induction fuel with
  | zero => intro x ρ t xy h; simp [globAux] at h
  | succ fuel ih =>
    intro x ρ t xy hxy
    rcases eq_or_ne ρ [] with rfl | hρ
    · rw [globAux_nil] at hxy; simp at hxy
    cases h : (P ρ).stop with
    | none =>
      rw [globAux_none P R fuel x hρ h] at hxy
      exact (hS.supp x ρ (hcov x) t xy hxy).1
    | some n =>
      have hA : (R x ρ).length = n := by rw [hR.len, acc_of_some h]
      rw [globAux_some P R fuel x hρ h] at hxy
      rcases mem_support_seqR hxy with ⟨_, h1⟩ | ⟨hle, y, _, h1⟩
      · exact (hS.supp x ρ (hcov x) t xy h1).1
      · intro r hr
        apply ih y _ _ xy h1 r
        rw [List.getElem?_drop, hA, Nat.add_sub_cancel' (by omega)]
        exact hr

omit hP hpos hR in
lemma globAux_cost (hC : 0 ≤ C) : ∀ (fuel : ℕ) (x : Config M) (ρ : List (Config M)),
    (chainCost v (globAux P R fuel x ρ) : ℝ) ≤ ncallsAux P fuel ρ * C := by
  intro fuel
  induction fuel with
  | zero => intro x ρ; simp only [globAux, chainCost_nil, NNReal.coe_zero]; positivity
  | succ fuel ih =>
    intro x ρ
    rcases eq_or_ne ρ [] with rfl | hρ
    · rw [globAux_nil]; simp only [chainCost_nil, NNReal.coe_zero]; positivity
    cases h : (P ρ).stop with
    | none =>
      rw [globAux_none P R fuel x hρ h, ncallsAux_none P fuel hρ h]
      simpa using hS.cost x ρ (hcov x)
    | some n =>
      rw [globAux_some P R fuel x hρ h, ncallsAux_some P fuel hρ h]
      refine (chainCost_seqR_le v _ _ _ _ (hS.chain x ρ (hcov x)) _
        fun y _ => ih y (ρ.drop n)).trans ?_
      have := hS.cost x ρ (hcov x)
      push_cast
      linarith

end GeneralizedUniformServer.Dev.WB.PartS
end
end

section
set_option autoImplicit false
open scoped NNReal
noncomputable section
namespace GeneralizedUniformServer.Dev.WB.PartS
open GeneralizedUniformServer.UnitWeights GeneralizedUniformServer.UnitWeights.Supplement
open GeneralizedUniformServer.Dev.WB
variable {k : ℕ} {M : Fin k → Type*}
lemma getLastD_eq_getD (l : List (Cpl M)) : l.getLastD 0 = l.getD (l.length - 1) 0 := by
  rcases l.eq_nil_or_concat with rfl | ⟨L, b, rfl⟩
  · rfl
  · simp [List.getD_eq_getElem?_getD]

end GeneralizedUniformServer.Dev.WB.PartS
end
end

section
set_option autoImplicit false
open scoped NNReal
noncomputable section
namespace GeneralizedUniformServer.Dev.WB.PartS
open GeneralizedUniformServer.UnitWeights GeneralizedUniformServer.UnitWeights.Supplement
open GeneralizedUniformServer.Dev.WB
/-!
# Part S: `strat_bound` (Lemma 5.4 and the algorithm of §5.5).

The fractional strategy `F.G h` is the last coupling of the global strategy on the prefix `h`:
consecutive `(k, ∅)`-phase strategies, each started from the end law of the previous one.
-/
theorem strat_bound {k : ℕ} {M : Fin k → Type*} [NeZero k] (hk : 2 ≤ k) (v : Fin k → ℝ≥0)
    (m : ℕ → ℕ) (hv : Normalized v m) (a : Config M) :
    ∃ F : FracStrat a, ∀ ρ : List (Config M),
      ∑ s ∈ Finset.range ρ.length, ((F.G (ρ.take (s + 1))).cost v : ℝ) ≤
        (ncalls m ρ : ℝ) * (10 * 5 ^ (k - 1)) * v (srv (k - 1)) := by
  have hk1 : k - 1 < k := by omega
  set U : PSet M := fun _ => none with hUdef
  set P := phase m (k - 1) U with hPdef
  set R := run v m (k - 1) U with hRdef
  have hS : SGood v (k - 1) U R (10 * 5 ^ (k - 1) * v (srv (k - 1))) :=
    level_sgood v m hv (k - 1) hk1 U (fun _ _ => rfl)
  have hPg : PGood P := phase_pgood m (k - 1) U
  have hPp : PPos P := phase_pos v m hv (k - 1) hk1 U
  have hRg : RGood P R := run_rgood v m (k - 1) U
  have hcov : ∀ x : Config M, Covers x U := fun x j u h => by simp [hUdef] at h
  set gl : List (Config M) → List (Cpl M) := fun h => globAux P R h.length a h with hgl
  have hlen : ∀ h, (gl h).length = h.length := fun h =>
    globAux_length P R hPg hPp hRg _ _ _ le_rfl
  have hon : ∀ ρ t, gl (ρ.take t) = (gl ρ).take t := by
    intro ρ t
    simp only [hgl]
    rw [globAux_fuel P R hPp _ ρ.length a _ le_rfl (by simp),
      globAux_online P R hPg hRg]
  have hch : ∀ h, IsChainD (Finsupp.single a 1) (gl h) := fun h =>
    globAux_chain P R hPg hPp hRg v _ U _ hS hcov _ _ _ le_rfl
  have hlast : ∀ h, (gl h).getLastD 0 = (gl h).getD (h.length - 1) 0 := fun h => by
    rw [getLastD_eq_getD, hlen]
  refine ⟨⟨fun h => (gl h).getLastD 0, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro h r
    rw [hlast, chain_mass_getD (hch _) (by rw [hlen]; simp), mass_single]
  · intro r
    rw [hlast]
    simpa using chain_getD_zero (hch [r]) (by rw [hlen]; simp)
  · intro h r hne
    rw [hlast, hlast]
    have hh : 1 ≤ h.length := List.length_pos_of_ne_nil hne
    have e1 : gl h = (gl (h ++ [r])).take h.length := by
      rw [← hon]; simp
    rw [e1, getD_take _ (by omega)]
    have := chain_getD_succ (hch (h ++ [r])) (t := h.length - 1) (by rw [hlen]; simp; omega)
    rw [show h.length - 1 + 1 = h.length by omega] at this
    simpa using this
  · intro h r xy hxy
    rw [hlast] at hxy
    exact globAux_serves P R hRg v _ U _ hS hcov _ _ _ _ xy hxy r (by simp)
  · intro ρ
    have hterm : ∀ s ∈ Finset.range ρ.length,
        (((gl (ρ.take (s + 1))).getLastD 0).cost v : ℝ) = (((gl ρ).getD s 0).cost v : ℝ) := by
      intro s hs
      rw [Finset.mem_range] at hs
      rw [hlast, hon, show (ρ.take (s + 1)).length - 1 = s by simp; omega,
        getD_take _ (by omega)]
    rw [Finset.sum_congr rfl hterm]
    have hc := globAux_cost P R v _ U _ hS hcov (by positivity) ρ.length a ρ
    rw [chainCost_eq_sum] at hc
    have hgl' : globAux P R ρ.length a ρ = gl ρ := rfl
    rw [hgl', hlen] at hc
    push_cast at hc
    have hn : ncalls m ρ = ncallsAux P ρ.length ρ := rfl
    rw [hn]
    calc _ ≤ _ := hc
      _ = _ := by ring

end GeneralizedUniformServer.Dev.WB.PartS
end
end

section
open scoped NNReal
noncomputable section
namespace GeneralizedUniformServer.Dev.WB
open GeneralizedUniformServer.UnitWeights GeneralizedUniformServer.UnitWeights.Supplement
variable {k : ℕ} {M : Fin k → Type*}
alias strat_bound := GeneralizedUniformServer.Dev.WB.PartS.strat_bound

end GeneralizedUniformServer.Dev.WB
end
end

section
set_option autoImplicit false
open scoped NNReal
noncomputable section
namespace GeneralizedUniformServer.Dev.WB.PartS
open GeneralizedUniformServer.UnitWeights GeneralizedUniformServer.UnitWeights.Supplement
open GeneralizedUniformServer.Dev.WB

end GeneralizedUniformServer.Dev.WB.PartS
end
end

section
set_option autoImplicit false
open scoped NNReal
noncomputable section
namespace GeneralizedUniformServer.Dev.WB.PartL
open GeneralizedUniformServer.UnitWeights GeneralizedUniformServer.UnitWeights.Supplement
open GeneralizedUniformServer.Dev.WB
variable {k : ℕ} {M : Fin k → Type*}
/-!
# Part L, parser structure: Lemma 5.2 for the Blueprint's parser
-/
/-! ## The critical set -/
theorem crit_mono_succ {α : Type*} (V : α →₀ ℕ) (n : ℕ) : crit V n ⊆ crit V (n + 1) := by
  classical
  intro x hx
  rw [crit]
  split
  · exact Finset.mem_insert_of_mem hx
  · exact hx

theorem crit_card_le {α : Type*} (V : α →₀ ℕ) (n : ℕ) : (crit V n).card ≤ n := by
  classical
  induction n with
  | zero => simp [crit]
  | succ n ih =>
    rw [crit]
    split
    · exact (Finset.card_insert_le _ _).trans (by omega)
    · omega

/-- If `b` is not critical, the critical set is full and every critical point has demand at
least that of `b`. -/
theorem crit_full {α : Type*} (V : α →₀ ℕ) (n : ℕ) (b : α) (hb : b ∉ crit V n) :
    (crit V n).card = n ∧ ∀ p ∈ crit V n, V b ≤ V p := by
  classical
  induction n with
  | zero => simp [crit]
  | succ n ih =>
    have hbn : b ∉ crit V n := fun h => hb (crit_mono_succ V n h)
    have key : ∃ q, q ∉ crit V n ∧ ∀ q', q' ∉ crit V n → V q' ≤ V q := by
      classical
      obtain ⟨q, hqT, hq⟩ := Finset.exists_max_image (insert b (V.support \ crit V n)) V
        ⟨b, Finset.mem_insert_self _ _⟩
      refine ⟨q, ?_, ?_⟩
      · rcases Finset.mem_insert.1 hqT with h | h
        · rw [h]; exact hbn
        · exact (Finset.mem_sdiff.1 h).2
      · intro q' hq'
        by_cases h0 : V q' = 0
        · rw [h0]; exact Nat.zero_le _
        · exact hq q' (Finset.mem_insert_of_mem
            (Finset.mem_sdiff.2 ⟨Finsupp.mem_support_iff.2 h0, hq'⟩))
    obtain ⟨ih1, ih2⟩ := ih hbn
    rw [crit, dif_pos key] at hb ⊢
    have hc := Classical.choose_spec key
    refine ⟨?_, ?_⟩
    · rw [Finset.card_insert_of_notMem hc.1, ih1]
    · intro p hp
      rcases Finset.mem_insert.1 hp with h | h
      · rw [h]; exact hc.2 b hbn
      · exact ih2 p h

/-! ## Norms of demand vectors -/
/-- `‖V‖ = ∑_p V[p]`. -/
def nrm {α : Type*} : (α →₀ ℕ) →+ ℕ := Finsupp.liftAddHom fun _ => AddMonoidHom.id ℕ

theorem nrm_single {α : Type*} (a : α) (c : ℕ) : nrm (Finsupp.single a c) = c := by
  simp [nrm]

theorem sum_le_nrm {α : Type*} (f : α →₀ ℕ) (T : Finset α) : ∑ p ∈ T, f p ≤ nrm f := by
  classical
  have : nrm f = ∑ p ∈ f.support, f p := by
    simp [nrm, Finsupp.liftAddHom_apply, Finsupp.sum]
  rw [this]
  exact Finset.sum_le_sum_of_ne_zero fun x _ hx => Finsupp.mem_support_iff.2 hx

/-! ## `scan` and the level-0 phase -/
theorem scan_some (P : Config M → Prop) : ∀ (ρ : List (Config M)) (n : ℕ), scan P ρ = some n →
    (∀ t < n, ∀ r, ρ[t]? = some r → P r) ∧ ∃ r, ρ[n]? = some r ∧ ¬ P r
  | [], n, h => by simp [scan] at h
  | r :: ρ, n, h => by
    simp only [scan] at h
    split_ifs at h with hr
    · obtain ⟨n', hn', rfl⟩ := Option.map_eq_some_iff.1 h
      obtain ⟨h1, r', h2, h3⟩ := scan_some P ρ n' hn'
      refine ⟨fun t ht r'' hr'' => ?_, r', by simpa using h2, h3⟩
      cases t with
      | zero => simp at hr''; subst hr''; exact hr
      | succ t => exact h1 t (by omega) r'' (by simpa using hr'')
    · cases h
      exact ⟨fun t ht => absurd ht (Nat.not_lt_zero _), r, rfl, hr⟩

/-- Structure of a completed `(1, U)`-phase: its witness `rw` at index `w`. -/
theorem phase0_some [NeZero k] (U : PSet M) : ∀ (ρ : List (Config M)) (n : ℕ),
    (phase0 U ρ).stop = some n →
    ∃ w < n, ∃ rw : Config M, ρ[w]? = some rw ∧ ¬ Sat U rw ∧
      (∀ t < w, ∀ r, ρ[t]? = some r → Sat U r) ∧
      (∃ r, ρ[n]? = some r ∧ ¬ Sat (Function.update U (srv 0) (some (rw (srv 0)))) r) ∧
      (phase0 U ρ).dem = fun j => Finsupp.single (rw j) 1
  | [], n, h => by simp [phase0] at h
  | r :: ρ, n, h => by
    by_cases hr : Sat U r
    · have h' : (phase0 U ρ).stop.map (· + 1) = some n := by
        simpa [phase0, hr] using h
      obtain ⟨n', hn', rfl⟩ := Option.map_eq_some_iff.1 h'
      obtain ⟨w, hw, rw, h1, h2, h3, ⟨r', h4, h5⟩, h6⟩ := phase0_some U ρ n' hn'
      refine ⟨w + 1, by omega, rw, by simpa using h1, h2, ?_, ⟨r', by simpa using h4, h5⟩, ?_⟩
      · intro t ht r'' hr''
        cases t with
        | zero => simp at hr''; subst hr''; exact hr
        | succ t => exact h3 t (by omega) r'' (by simpa using hr'')
      · simp [phase0, hr, h6]
    · cases hs : scan (Sat (Function.update U (srv 0) (some (r (srv 0))))) ρ with
      | none => simp [phase0, hr, hs] at h
      | some n' =>
        have hn : n = n' + 1 := by
          simp [phase0, hr, hs] at h; omega
        subst hn
        obtain ⟨_, r', h4, h5⟩ := scan_some _ ρ n' hs
        refine ⟨0, by omega, r, rfl, hr, fun t ht => absurd ht (Nat.not_lt_zero _),
          ⟨r', by simpa using h4, h5⟩, ?_⟩
        simp [phase0, hr, hs]

/-! ## Multiphases -/
/-- Offset of the `s`-th part of the multiphase `iter f _ ρ`. -/
def off (f : List (Config M) → PR M) (ρ : List (Config M)) : ℕ → ℕ
  | 0 => 0
  | s + 1 => off f ρ s + (f (ρ.drop (off f ρ s))).stop.getD 0

theorem off_succ' (f : List (Config M) → PR M) (ρ : List (Config M)) (s : ℕ) :
    off f ρ (s + 1) = (f ρ).stop.getD 0 + off f (ρ.drop ((f ρ).stop.getD 0)) s := by
  induction s with
  | zero => simp [off]
  | succ s ih =>
    rw [off, ih, off, List.drop_drop]
    omega

theorem iter_some (f : List (Config M) → PR M) : ∀ (m : ℕ) (ρ : List (Config M)) (N : ℕ),
    (iter f m ρ).stop = some N →
    (∀ s < m, ∃ ns, (f (ρ.drop (off f ρ s))).stop = some ns) ∧ N = off f ρ m ∧
    (iter f m ρ).dem = ∑ s ∈ Finset.range m, (f (ρ.drop (off f ρ s))).dem
  | 0, ρ, N, h => by
    simp only [iter, Option.some.injEq] at h
    subst h
    simp [iter, off]
  | m + 1, ρ, N, h => by
    cases hf : (f ρ).stop with
    | none => simp [iter, hf] at h
    | some n =>
      have h' : (iter f m (ρ.drop n)).stop.map (n + ·) = some N := by
        simpa [iter, hf] using h
      obtain ⟨N', hN', rfl⟩ := Option.map_eq_some_iff.1 h'
      obtain ⟨i1, i2, i3⟩ := iter_some f m (ρ.drop n) N' hN'
      have hoff : ∀ s, off f ρ (s + 1) = n + off f (ρ.drop n) s := by
        intro s; rw [off_succ', hf]; rfl
      refine ⟨?_, ?_, ?_⟩
      · intro s hs
        cases s with
        | zero => exact ⟨n, by simpa [off] using hf⟩
        | succ s =>
          obtain ⟨ns, hns⟩ := i1 s (by omega)
          exact ⟨ns, by rw [hoff, ← List.drop_drop]; exact hns⟩
      · rw [hoff, i2]
      · have e1 : (iter f (m + 1) ρ).dem = (f ρ).dem + (iter f m (ρ.drop n)).dem := by
          simp [iter, hf]
        rw [e1, i3, Finset.sum_range_succ']
        rw [show off f ρ 0 = 0 from rfl, List.drop_zero, add_comm]
        congr 1
        refine Finset.sum_congr rfl fun s _ => ?_
        rw [hoff, ← List.drop_drop]

theorem off_step (f : List (Config M) → PR M) (ρ : List (Config M)) (s ns : ℕ)
    (h : (f (ρ.drop (off f ρ s))).stop = some ns) : off f ρ (s + 1) = off f ρ s + ns := by
  rw [off, h]; rfl

end GeneralizedUniformServer.Dev.WB.PartL
end
end

section
set_option autoImplicit false
open scoped NNReal
noncomputable section
namespace GeneralizedUniformServer.Dev.WB.PartL
open GeneralizedUniformServer.UnitWeights GeneralizedUniformServer.UnitWeights.Supplement
open GeneralizedUniformServer.Dev.WB
variable {k : ℕ} {M : Fin k → Type*}
variable [NeZero k] (m : ℕ → ℕ)
/-! ## Phases of level `L + 1` -/
/-- The explore part. -/
def Ex (L : ℕ) (U : PSet M) (ρ : List (Config M)) : PR M := iter (phase m L U) (m L) ρ

/-- Where the explore part stops. -/
def eS (L : ℕ) (U : PSet M) (ρ : List (Config M)) : ℕ := (Ex m L U ρ).stop.getD 0

/-- The critical set. -/
def Sc (L : ℕ) (U : PSet M) (ρ : List (Config M)) : Finset (M (srv (L + 1))) :=
  crit ((Ex m L U ρ).dem (srv (L + 1))) (D (L + 1) - 1)

/-- The exploit part for `p`. -/
def Xp (L : ℕ) (U : PSet M) (ρ : List (Config M)) (p : M (srv (L + 1))) : PR M :=
  iter (phase m L (Function.update U (srv (L + 1)) (some p))) (m L) (ρ.drop (eS m L U ρ))

theorem phase_zero (U : PSet M) (ρ : List (Config M)) : phase m 0 U ρ = phase0 U ρ := by
  rw [phase]

theorem phase_succ_some (L : ℕ) (U : PSet M) (ρ : List (Config M)) (n : ℕ)
    (h : (phase m (L + 1) U ρ).stop = some n) :
    (Ex m L U ρ).stop = some (eS m L U ρ) ∧
    (∀ p ∈ Sc m L U ρ, ∃ np, (Xp m L U ρ p).stop = some np ∧ eS m L U ρ + np ≤ n) ∧
    eS m L U ρ ≤ n ∧
    (phase m (L + 1) U ρ).dem = (Ex m L U ρ).dem + ∑ p ∈ Sc m L U ρ, (Xp m L U ρ p).dem := by
  cases hE : (iter (phase m L U) (m L) ρ).stop with
  | none => simp [phase, hE] at h
  | some e =>
    have hEx : (Ex m L U ρ).stop = some e := hE
    have he : eS m L U ρ = e := by simp [eS, hEx]
    rw [phase] at h ⊢
    simp only [hE] at h ⊢
    split_ifs at h ⊢ with hc
    · simp only [Option.some.injEq] at h
      refine ⟨by rw [hEx, he], ?_, by rw [he]; omega, ?_⟩
      swap
      · simp only [Xp, Sc, Ex, he]
      intro p hp
      have hp' := hc p hp
      obtain ⟨np, hnp⟩ := Option.ne_none_iff_exists'.1 hp'
      refine ⟨np, ?_, ?_⟩
      · simp only [Xp, he]; exact hnp
      · rw [he, ← h]
        have := Finset.le_sup (f := fun p => ((iter (phase m L (Function.update U (srv (L + 1))
          (some p))) (m L) (List.drop e ρ)).stop.getD 0)) hp
        simp only [hnp, Option.getD_some] at this
        simp only [Sc, Ex] at this ⊢
        omega

theorem srv_val (i : ℕ) (hi : i < k) : (srv (k := k) i).val = i := Nat.mod_eq_of_lt hi

theorem D_pos (i : ℕ) : 0 < D i := by unfold D; positivity

/-- The nominal `κ` (Lemma 5.2(d)). -/
def kap : ℕ → ℕ
  | 0 => 1
  | L + 1 => D (L + 1) * m L * kap L

theorem iter_nrm (L : ℕ)
    (hL : ∀ (U : PSet M) (ρ : List (Config M)) (n : ℕ), (phase m L U ρ).stop = some n →
      ∀ j, nrm ((phase m L U ρ).dem j) ≤ kap m L)
    (U : PSet M) (ρ : List (Config M)) (N : ℕ) (h : (iter (phase m L U) (m L) ρ).stop = some N)
    (j : Fin k) : nrm ((iter (phase m L U) (m L) ρ).dem j) ≤ m L * kap m L := by
  obtain ⟨h1, -, h3⟩ := iter_some _ _ _ _ h
  rw [h3, Finset.sum_apply, map_sum]
  calc _ ≤ ∑ s ∈ Finset.range (m L), kap m L := Finset.sum_le_sum fun s hs => by
          obtain ⟨ns, hns⟩ := h1 s (Finset.mem_range.1 hs); exact hL _ _ _ hns j
    _ = _ := by simp

/-- Lemma 5.2(d), first half, with `≤`. -/
theorem phase_nrm : ∀ (L : ℕ) (U : PSet M) (ρ : List (Config M)) (n : ℕ),
    (phase m L U ρ).stop = some n → ∀ j, nrm ((phase m L U ρ).dem j) ≤ kap m L
  | 0, U, ρ, n, h, j => by
    rw [phase_zero] at h ⊢
    obtain ⟨w, -, rw, -, -, -, -, hd⟩ := phase0_some U ρ n h
    rw [hd, nrm_single]; simp [kap]
  | L + 1, U, ρ, n, h, j => by
    obtain ⟨hE, hX, -, hd⟩ := phase_succ_some m L U ρ n h
    have ih := phase_nrm L
    rw [hd, Pi.add_apply, Finset.sum_apply, map_add, map_sum]
    have h1 := iter_nrm m L ih U ρ _ hE j
    have h2 : ∀ p ∈ Sc m L U ρ, nrm ((Xp m L U ρ p).dem j) ≤ m L * kap m L := fun p hp => by
      obtain ⟨np, hnp, -⟩ := hX p hp; exact iter_nrm m L ih _ _ _ hnp j
    have h3 := Finset.sum_le_sum h2
    rw [Finset.sum_const, smul_eq_mul] at h3
    have h4 := crit_card_le ((Ex m L U ρ).dem (srv (L + 1))) (D (L + 1) - 1)
    have h5 := D_pos (L + 1)
    have h6 : (Sc m L U ρ).card * (m L * kap m L) ≤ (D (L + 1) - 1) * (m L * kap m L) :=
      Nat.mul_le_mul_right _ h4
    have h1' : nrm ((Ex m L U ρ).dem j) ≤ m L * kap m L := h1
    obtain ⟨d, hd⟩ : ∃ d, D (L + 1) = d + 1 := ⟨D (L + 1) - 1, by omega⟩
    simp only [kap]
    rw [hd] at h6 ⊢
    simp only [add_tsub_cancel_right] at h6
    nlinarith

/-- `U` has no point on servers `≤ L`. -/
def Low (L : ℕ) (U : PSet M) : Prop := ∀ j : Fin k, j.val ≤ L → U j = none

omit [NeZero k] in
theorem low_mono (L : ℕ) (U : PSet M) (h : Low (L + 1) U) : Low L U :=
  fun j hj => h j (by omega)

theorem low_update (L : ℕ) (hL : L + 1 < k) (U : PSet M) (hU : Low (L + 1) U)
    (p : M (srv (L + 1))) : Low L (Function.update U (srv (L + 1)) (some p)) := by
  intro j hj
  have : j ≠ srv (L + 1) := by
    intro h
    have := congrArg Fin.val h
    rw [srv_val _ hL] at this
    omega
  rw [Function.update_of_ne this]
  exact hU j (by omega)

theorem iter_vanish (L : ℕ)
    (hL : ∀ (U : PSet M) (ρ : List (Config M)) (n : ℕ), Low L U → (phase m L U ρ).stop = some n →
      ∀ j u, U j = some u → (phase m L U ρ).dem j u = 0)
    (U : PSet M) (ρ : List (Config M)) (N : ℕ) (hU : Low L U)
    (h : (iter (phase m L U) (m L) ρ).stop = some N) (j : Fin k) (u : M j) (hu : U j = some u) :
    (iter (phase m L U) (m L) ρ).dem j u = 0 := by
  obtain ⟨h1, -, h3⟩ := iter_some _ _ _ _ h
  rw [h3, Finset.sum_apply, Finsupp.finsetSum_apply]
  refine Finset.sum_eq_zero fun s hs => ?_
  obtain ⟨ns, hns⟩ := h1 s (Finset.mem_range.1 hs)
  exact hL _ _ _ hU hns j u hu

/-- Lemma 5.2(d), second half: demand vanishes on `U`. -/
theorem phase_vanish : ∀ (L : ℕ), L < k → ∀ (U : PSet M) (ρ : List (Config M)) (n : ℕ),
    Low L U → (phase m L U ρ).stop = some n →
    ∀ j u, U j = some u → (phase m L U ρ).dem j u = 0
  | 0, _, U, ρ, n, _, h, j, u, hu => by
    rw [phase_zero] at h ⊢
    obtain ⟨w, -, rw, -, hns, -, -, hd⟩ := phase0_some U ρ n h
    rw [hd]
    have : rw j ≠ u := fun e => hns ⟨j, by rw [hu, e]⟩
    classical
    simp only
    rw [Finsupp.single_apply, if_neg this]
  | L + 1, hL, U, ρ, n, hU, h, j, u, hu => by
    obtain ⟨hE, hX, -, hd⟩ := phase_succ_some m L U ρ n h
    have ih := phase_vanish L (by omega)
    rw [hd, Pi.add_apply, Finsupp.add_apply, Finset.sum_apply, Finsupp.finsetSum_apply]
    have hjn : j ≠ srv (L + 1) := by
      intro e
      subst e
      rw [hU _ (by rw [srv_val _ hL])] at hu
      exact absurd hu (by simp)
    rw [show (Ex m L U ρ).dem j u = 0 from iter_vanish m L ih U ρ _ (low_mono L U hU) hE j u hu,
      zero_add]
    refine Finset.sum_eq_zero fun p hp => ?_
    obtain ⟨np, hnp, -⟩ := hX p hp
    refine iter_vanish m L ih _ _ _ (low_update L hL U hU p) hnp j u ?_
    rw [Function.update_of_ne hjn]; exact hu

/-! ## The hard multiphase `Q(P, ξ)` -/
open Classical in
/-- Offset of the hard multiphase. -/
def qOff (L : ℕ) (U : PSet M) (ρ : List (Config M)) (ξ : ℕ → Config M) : ℕ :=
  if ξ 0 (srv (L + 1)) ∈ Sc m L U ρ then eS m L U ρ else 0

open Classical in
/-- The set `U` of the hard multiphase. -/
def qU (L : ℕ) (U : PSet M) (ρ : List (Config M)) (ξ : ℕ → Config M) : PSet M :=
  if ξ 0 (srv (L + 1)) ∈ Sc m L U ρ then Function.update U (srv (L + 1)) (some (ξ 0 (srv (L + 1))))
  else U

/-- Offset (in `ρ`) of the `s`-th phase of the hard multiphase. -/
def qOffs (L : ℕ) (U : PSet M) (ρ : List (Config M)) (ξ : ℕ → Config M) (s : ℕ) : ℕ :=
  qOff m L U ρ ξ + off (phase m L (qU m L U ρ ξ)) (ρ.drop (qOff m L U ρ ξ)) s

theorem Q_sub (L : ℕ) (U : PSet M) (ρ : List (Config M)) (n : ℕ) (ξ : ℕ → Config M)
    (h : (phase m (L + 1) U ρ).stop = some n) :
    (∀ s < m L, ∃ ns, (phase m L (qU m L U ρ ξ) (ρ.drop (qOffs m L U ρ ξ s))).stop = some ns ∧
      qOffs m L U ρ ξ (s + 1) = qOffs m L U ρ ξ s + ns) ∧
    qOffs m L U ρ ξ (m L) ≤ n ∧
    ∀ j b, ∑ s ∈ Finset.range (m L), (phase m L (qU m L U ρ ξ) (ρ.drop (qOffs m L U ρ ξ s))).dem j b
      ≤ (phase m (L + 1) U ρ).dem j b := by
  obtain ⟨hE, hX, heS, hd⟩ := phase_succ_some m L U ρ n h
  have gen : ∀ (q : ℕ) (U' : PSet M) (N : ℕ), (iter (phase m L U') (m L) (ρ.drop q)).stop = some N →
      q + N ≤ n →
      (∀ j b, (iter (phase m L U') (m L) (ρ.drop q)).dem j b ≤ (phase m (L + 1) U ρ).dem j b) →
      (∀ s < m L, ∃ ns, (phase m L U' (ρ.drop (q + off (phase m L U') (ρ.drop q) s))).stop = some ns ∧
        q + off (phase m L U') (ρ.drop q) (s + 1) = q + off (phase m L U') (ρ.drop q) s + ns) ∧
      q + off (phase m L U') (ρ.drop q) (m L) ≤ n ∧
      ∀ j b, ∑ s ∈ Finset.range (m L),
        (phase m L U' (ρ.drop (q + off (phase m L U') (ρ.drop q) s))).dem j b
          ≤ (phase m (L + 1) U ρ).dem j b := by
    intro q U' N hN hle hdem
    obtain ⟨i1, i2, i3⟩ := iter_some _ _ _ _ hN
    refine ⟨fun s hs => ?_, by rw [← i2]; exact hle, fun j b => ?_⟩
    · obtain ⟨ns, hns⟩ := i1 s hs
      refine ⟨ns, by rw [← List.drop_drop]; exact hns, by rw [off_step _ _ _ _ hns]; ring⟩
    · have := hdem j b
      rw [i3, Finset.sum_apply, Finsupp.finsetSum_apply] at this
      simpa only [List.drop_drop] using this
  by_cases hb : ξ 0 (srv (L + 1)) ∈ Sc m L U ρ
  · have e1 : qOff m L U ρ ξ = eS m L U ρ := if_pos hb
    have e2 : qU m L U ρ ξ = Function.update U (srv (L + 1)) (some (ξ 0 (srv (L + 1)))) :=
      if_pos hb
    simp only [qOffs, e1, e2]
    obtain ⟨np, hnp, hle⟩ := hX _ hb
    refine gen _ _ np hnp hle fun j b => ?_
    rw [hd, Pi.add_apply, Finsupp.add_apply, Finset.sum_apply, Finsupp.finsetSum_apply]
    exact le_add_left (Finset.single_le_sum (f := fun p => (Xp m L U ρ p).dem j b)
      (fun _ _ => Nat.zero_le _) hb)
  · have e1 : qOff m L U ρ ξ = 0 := if_neg hb
    have e2 : qU m L U ρ ξ = U := if_neg hb
    simp only [qOffs, e1, e2]
    refine gen 0 U _ (by rw [List.drop_zero]; exact hE) (by omega) fun j b => ?_
    rw [hd, Pi.add_apply, Finsupp.add_apply, List.drop_zero]
    exact le_add_right le_rfl

theorem qOffs_mono (L : ℕ) (U : PSet M) (ρ : List (Config M)) (ξ : ℕ → Config M) (n : ℕ)
    (h : (phase m (L + 1) U ρ).stop = some n) (s s' : ℕ) (hss : s ≤ s') (hs' : s' ≤ m L) :
    qOffs m L U ρ ξ s ≤ qOffs m L U ρ ξ s' := by
  obtain ⟨h1, -, -⟩ := Q_sub m L U ρ n ξ h
  induction s', hss using Nat.le_induction with
  | base => exact le_rfl
  | succ s' hss ih =>
    obtain ⟨ns, -, hns⟩ := h1 s' (by omega)
    rw [hns]; exact (ih (by omega)).trans (Nat.le_add_right _ _)

theorem qU_low (L : ℕ) (hL : L + 1 < k) (U : PSet M) (ρ : List (Config M)) (ξ : ℕ → Config M)
    (hU : Low (L + 1) U) : Low L (qU m L U ρ ξ) := by
  unfold qU
  split_ifs
  · exact low_update L hL U hU _
  · exact low_mono L U hU

end GeneralizedUniformServer.Dev.WB.PartL
end
end

section
set_option autoImplicit false
open scoped NNReal
noncomputable section
namespace GeneralizedUniformServer.Dev.WB.PartL
open GeneralizedUniformServer.UnitWeights GeneralizedUniformServer.UnitWeights.Supplement
open GeneralizedUniformServer.Dev.WB
variable {k : ℕ} {M : Fin k → Type*}
/-!
# Part L, contamination: Definition 5.5, Lemmas 5.6–5.8
-/
/-- Shift of a solution: the restriction starting at index `a`. -/
def sh (ξ : ℕ → Config M) (a : ℕ) : ℕ → Config M := fun t => ξ (a + t)

end GeneralizedUniformServer.Dev.WB.PartL
end
end

section
set_option autoImplicit false
open scoped NNReal
noncomputable section
namespace GeneralizedUniformServer.Dev.WB.PartL
open GeneralizedUniformServer.UnitWeights GeneralizedUniformServer.UnitWeights.Supplement
open GeneralizedUniformServer.Dev.WB
variable {k : ℕ} {M : Fin k → Type*}
variable (v : Fin k → ℝ≥0) (ξ : ℕ → Config M)
theorem cI_sh (a n : ℕ) : cI v (sh ξ a) 0 n = cI v ξ a (a + n) := by
  unfold cI sh
  rw [Finset.sum_Ico_eq_sum_range, Finset.sum_Ico_eq_sum_range]
  simp [add_assoc]

theorem cI_consec (c : ℕ → ℕ) : ∀ p : ℕ, (∀ s < p, c s ≤ c (s + 1)) →
    ∑ s ∈ Finset.range p, cI v ξ (c s) (c (s + 1)) = cI v ξ (c 0) (c p) ∧ c 0 ≤ c p
  | 0, _ => by simp [cI]
  | p + 1, hc => by
    obtain ⟨ih1, ih2⟩ := cI_consec c p fun s hs => hc s (by omega)
    have := hc p (by omega)
    refine ⟨?_, by omega⟩
    rw [Finset.sum_range_succ, ih1, cI_add v ξ ih2 this]

theorem wdist_ge (x y : Config M) (j : Fin k) (h : x j ≠ y j) : v j ≤ wdist v x y := by
  classical
  unfold wdist
  refine le_trans ?_ (Finset.single_le_sum (fun i _ => zero_le) (Finset.mem_univ j))
  simp [h]

theorem move_cost (j : Fin k) (a b : ℕ) (hab : a ≤ b) (h : ξ a j ≠ ξ b j) :
    (v j : ℝ) ≤ cI v ξ a b := by
  induction b, hab using Nat.le_induction with
  | base => exact absurd rfl h
  | succ b hab ih =>
    by_cases h' : ξ a j = ξ b j
    · have hb : ξ b j ≠ ξ (b + 1) j := by rw [← h']; exact h
      calc (v j : ℝ) ≤ wdist v (ξ b) (ξ (b + 1)) := by exact_mod_cast wdist_ge v _ _ j hb
        _ = cI v ξ b (b + 1) := by simp [cI]
        _ ≤ cI v ξ a (b + 1) := cI_mono v ξ hab le_rfl
    · exact (ih h').trans (cI_mono v ξ le_rfl (by omega))

theorem sol_sh (ρ : List (Config M)) (n a ns : ℕ) (h : Sol ρ n ξ) (hle : a + ns ≤ n) :
    Sol (ρ.drop a) ns (sh ξ a) := by
  intro t ht r hr
  rw [List.getElem?_drop] at hr
  have := h (a + t) (by omega) r hr
  simpa [sh, add_assoc] using this

end GeneralizedUniformServer.Dev.WB.PartL
end
end

section
set_option autoImplicit false
open scoped NNReal
noncomputable section
namespace GeneralizedUniformServer.Dev.WB.PartL
open GeneralizedUniformServer.UnitWeights GeneralizedUniformServer.UnitWeights.Supplement
open GeneralizedUniformServer.Dev.WB
variable {k : ℕ} {M : Fin k → Type*}
variable [NeZero k] (m : ℕ → ℕ) (v : Fin k → ℝ≥0)
/-! ## Normalized weights -/
theorem srv_eq (i : ℕ) (hi : i < k) : (srv i : Fin k) = ⟨i, hi⟩ := Fin.ext (srv_val i hi)

theorem v_succ (hv : Normalized v m) (L : ℕ) (hL : L + 1 < k) :
    v (srv (L + 1)) = m L * v (srv L) := by
  rw [srv_eq _ hL, srv_eq L (by omega)]; exact (hv.2 L hL).2

theorem v_mono (hv : Normalized v m) (i : ℕ) (hi : i < k) (j : Fin k) (hij : i ≤ j.val) :
    v (srv i) ≤ v j := by
  obtain ⟨j, hj⟩ := j
  simp only at hij
  revert hj
  induction j, hij using Nat.le_induction with
  | base => intro hj; rw [srv_eq _ hi]
  | succ j hij ih =>
    intro hj
    have h1 := (hv.2 j hj).1
    have h2 := (hv.2 j hj).2
    have hm1 : (1 : ℝ≥0) ≤ m j := by exact_mod_cast (by omega : 1 ≤ m j)
    calc v (srv i) ≤ v ⟨j, by omega⟩ := ih (by omega)
      _ = 1 * v ⟨j, by omega⟩ := (one_mul _).symm
      _ ≤ m j * v ⟨j, by omega⟩ := by gcongr
      _ = v ⟨j + 1, hj⟩ := h2.symm

end GeneralizedUniformServer.Dev.WB.PartL
end
end

section
set_option autoImplicit false
open scoped NNReal
noncomputable section
namespace GeneralizedUniformServer.Dev.WB.PartL
open GeneralizedUniformServer.UnitWeights GeneralizedUniformServer.UnitWeights.Supplement
open GeneralizedUniformServer.Dev.WB
variable {k : ℕ} {M : Fin k → Type*}
/-! ## `Γ` and Lemma 5.6 -/
/-- `Γ_{ℓ,j}` at level index `L = ℓ - 1` and server index `j` (paper `j + 1`). -/
def Gam : ℕ → ℕ → ℕ
  | 0, _ => 1
  | L + 1, j => 2 ^ (j + 2 - L) * D L * Gam L j

/-- Exponent of `Γ`. -/
def gE : ℕ → ℕ → ℕ
  | 0, _ => 0
  | L + 1, j => (j + 2 - L) + (5 ^ L - 1) + gE L j

theorem Gam_eq (L j : ℕ) : Gam L j = 2 ^ gE L j := by
  induction L with
  | zero => simp [Gam, gE]
  | succ L ih => rw [Gam, gE, ih, D, pow_add, pow_add]

theorem gE_formula (j : ℕ) : ∀ L, L ≤ j → 4 * gE L j + 2 * L ^ 2 + 1 = 4 * L * j + 6 * L + 5 ^ L
  | 0, _ => by simp [gE]
  | L + 1, h => by
    have ih := gE_formula j L (by omega)
    have h5 : 1 ≤ 5 ^ L := Nat.one_le_pow _ _ (by norm_num)
    rw [gE, pow_succ 5 L]
    obtain ⟨a, ha⟩ : ∃ a, j + 2 - L = a ∧ a + L = j + 2 := ⟨j + 2 - L, rfl, by omega⟩
    obtain ⟨c, hc⟩ : ∃ c, 5 ^ L - 1 = c ∧ c + 1 = 5 ^ L := ⟨5 ^ L - 1, rfl, by omega⟩
    rw [ha.1, hc.1]
    have e1 := ha.2
    have e2 := hc.2
    clear ha hc
    zify at ih e1 e2 ⊢
    linear_combination ih + 4 * e1 + 4 * e2

theorem pow5_bound : ∀ L : ℕ, 2 * L ^ 2 + 10 * L + 15 ≤ 15 * 5 ^ L
  | 0 => by norm_num
  | L + 1 => by
    have := pow5_bound L
    rw [pow_succ 5 L]
    nlinarith

/-- Lemma 5.6, in the form used: `16 d_{ℓ-1} Γ_{ℓ-1,ℓ} = 2 Γ_{ℓ,ℓ} ≤ d_ℓ`. -/
theorem lem56 (L : ℕ) : 16 * D L * Gam L (L + 1) ≤ D (L + 1) := by
  have hf := gE_formula (L + 1) L (by omega)
  have hp := pow5_bound L
  have h5 : 1 ≤ 5 ^ L := Nat.one_le_pow _ _ (by norm_num)
  rw [Gam_eq, D, D, show (16 : ℕ) = 2 ^ 4 by norm_num, ← pow_add, ← pow_add]
  apply Nat.pow_le_pow_right (by norm_num)
  rw [pow_succ]
  obtain ⟨c, hc⟩ : ∃ c, 5 ^ L - 1 = c ∧ c + 1 = 5 ^ L := ⟨5 ^ L - 1, rfl, by omega⟩
  obtain ⟨c', hc'⟩ : ∃ c', 5 ^ L * 5 - 1 = c' ∧ c' + 1 = 5 ^ L * 5 := ⟨_, rfl, by omega⟩
  rw [hc.1, hc'.1]
  nlinarith [hc.2, hc'.2]

end GeneralizedUniformServer.Dev.WB.PartL
end
end

section
set_option autoImplicit false
open scoped NNReal
noncomputable section
namespace GeneralizedUniformServer.Dev.WB.PartL
open GeneralizedUniformServer.UnitWeights GeneralizedUniformServer.UnitWeights.Supplement
open GeneralizedUniformServer.Dev.WB
variable {k : ℕ} {M : Fin k → Type*}
variable [NeZero k] (m : ℕ → ℕ)
open Classical in
/-- Definition 5.5: `ξ` is `j`-contaminated for the level-`L` phase on `ρ` with set `U`. -/
def contam : ℕ → PSet M → List (Config M) → (ℕ → Config M) → Fin k → Prop
  | 0, U, ρ, ξ, j => (phase0 U ρ).dem j (ξ 0 j) ≠ 0
  | L + 1, U, ρ, ξ, j => m L ≤ 2 ^ (j.val + 2 - L) *
      ((Finset.range (m L)).filter fun s => contam L (qU m L U ρ ξ) (ρ.drop (qOffs m L U ρ ξ s))
        (sh ξ (qOffs m L U ρ ξ s)) j).card

end GeneralizedUniformServer.Dev.WB.PartL
end
end

section
set_option autoImplicit false
open scoped NNReal
noncomputable section
namespace GeneralizedUniformServer.Dev.WB.PartL
open GeneralizedUniformServer.UnitWeights GeneralizedUniformServer.UnitWeights.Supplement
open GeneralizedUniformServer.Dev.WB
variable {k : ℕ} {M : Fin k → Type*}
variable [NeZero k] (m : ℕ → ℕ) (v : Fin k → ℝ≥0)
/-! ## Lemma 5.9 -/
/-- A phase of the hard multiphase is good if its restriction is not `j`-contaminated for any
`j ≥ ℓ` (paper indexing). -/
def good (L : ℕ) (U : PSet M) (ρ : List (Config M)) (ξ : ℕ → Config M) (s : ℕ) : Prop :=
  ∀ j : Fin k, L + 1 ≤ j.val →
    ¬ contam m L (qU m L U ρ ξ) (ρ.drop (qOffs m L U ρ ξ s)) (sh ξ (qOffs m L U ρ ξ s)) j

open Classical in
/-- The phases of the hard multiphase that are not good. -/
def badS (L : ℕ) (U : PSet M) (ρ : List (Config M)) (ξ : ℕ → Config M) : Finset ℕ :=
  (Finset.range (m L)).filter fun s => ¬ good m L U ρ ξ s

omit [NeZero k] in
theorem geom_bound (L k' : ℕ) :
    ∑ t ∈ Finset.range k', (if L + 1 < t then (1 / 2 : ℝ) ^ (t + 2 - L) else 0) ≤ 1 / 8 := by
  calc _ ≤ ∑ t ∈ Finset.range (L + 2 + k'), (if L + 1 < t then (1 / 2 : ℝ) ^ (t + 2 - L) else 0) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 (by omega))
          (fun _ _ _ => by split_ifs <;> positivity)
    _ = ∑ u ∈ Finset.range k', (1 / 2 : ℝ) ^ (u + 4) := by
        rw [Finset.sum_range_add]
        rw [Finset.sum_eq_zero (fun t ht => if_neg (by simp at ht; omega)), zero_add]
        refine Finset.sum_congr rfl fun u _ => ?_
        rw [if_pos (by omega)]
        congr 1
        omega
    _ = (1 / 16) * ∑ u ∈ Finset.range k', (1 / 2 : ℝ) ^ u := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun u _ => ?_
        rw [pow_add]; norm_num; ring
    _ ≤ (1 / 16) * 2 := by gcongr; exact sum_geometric_two_le k'
    _ = 1 / 8 := by norm_num

end GeneralizedUniformServer.Dev.WB.PartL
end
end

section
set_option autoImplicit false
open scoped NNReal
noncomputable section
namespace GeneralizedUniformServer.Dev.WB.PartL
open GeneralizedUniformServer.UnitWeights GeneralizedUniformServer.UnitWeights.Supplement
open GeneralizedUniformServer.Dev.WB
variable {k : ℕ} {M : Fin k → Type*}
variable [NeZero k] (m : ℕ → ℕ)
open Classical in
/-- The phases of the hard multiphase whose restriction is `j`-contaminated. -/
def cset (L : ℕ) (U : PSet M) (ρ : List (Config M)) (ξ : ℕ → Config M) (j : Fin k) : Finset ℕ :=
  (Finset.range (m L)).filter fun s => contam m L (qU m L U ρ ξ) (ρ.drop (qOffs m L U ρ ξ s))
    (sh ξ (qOffs m L U ρ ξ s)) j

theorem contam_succ (L : ℕ) (U : PSet M) (ρ : List (Config M)) (ξ : ℕ → Config M) (j : Fin k) :
    contam m (L + 1) U ρ ξ j ↔ m L ≤ 2 ^ (j.val + 2 - L) * (cset m L U ρ ξ j).card := by
  rw [contam, cset]

theorem mem_cset (L : ℕ) (U : PSet M) (ρ : List (Config M)) (ξ : ℕ → Config M) (j : Fin k)
    (s : ℕ) : s ∈ cset m L U ρ ξ j ↔ s < m L ∧ contam m L (qU m L U ρ ξ)
      (ρ.drop (qOffs m L U ρ ξ s)) (sh ξ (qOffs m L U ρ ξ s)) j := by
  classical
  rw [cset, Finset.mem_filter, Finset.mem_range]

theorem cset_sub (L : ℕ) (U : PSet M) (ρ : List (Config M)) (ξ : ℕ → Config M) (j : Fin k) :
    cset m L U ρ ξ j ⊆ Finset.range (m L) := fun s hs =>
  Finset.mem_range.2 ((mem_cset m L U ρ ξ j s).1 hs).1

theorem kap_pos (L : ℕ) (hm : ∀ i, i < L → 1 ≤ m i) : 0 < kap m L := by
  induction L with
  | zero => simp [kap]
  | succ L ih =>
    simp only [kap]
    have := ih (fun i hi => hm i (by omega))
    have := hm L (by omega)
    have := D_pos (L + 1)
    positivity

/-- Each phase of the hard multiphase stays inside `P`'s interval. -/
theorem sub_in (L : ℕ) (U : PSet M) (ρ : List (Config M)) (n : ℕ) (ξ : ℕ → Config M)
    (h : (phase m (L + 1) U ρ).stop = some n) (s : ℕ) (hs : s < m L) :
    ∃ ns, (phase m L (qU m L U ρ ξ) (ρ.drop (qOffs m L U ρ ξ s))).stop = some ns ∧
      qOffs m L U ρ ξ (s + 1) = qOffs m L U ρ ξ s + ns ∧ qOffs m L U ρ ξ s + ns ≤ n := by
  obtain ⟨h1, h2, -⟩ := Q_sub m L U ρ n ξ h
  obtain ⟨ns, hns, hstep⟩ := h1 s hs
  have := qOffs_mono m L U ρ ξ n h (s + 1) (m L) hs le_rfl
  exact ⟨ns, hns, hstep, by omega⟩

/-- Lemma 5.7 with the nominal `κ`: `κ_ℓ ≤ V[b] d_ℓ Γ_{ℓ,j}`. -/
theorem lem57 : ∀ (L : ℕ) (U : PSet M) (ρ : List (Config M)) (n : ℕ) (ξ : ℕ → Config M)
    (j : Fin k) (b : M j),
    (phase m L U ρ).stop = some n → L < j.val → (∀ t ≤ n, ξ t j = b) → contam m L U ρ ξ j →
    kap m L ≤ (phase m L U ρ).dem j b * D L * Gam L j.val
  | 0, U, ρ, n, ξ, j, b, h, _, hb, hc => by
    have e : ξ 0 j = b := hb 0 (Nat.zero_le _)
    simp only [contam, e] at hc
    rw [phase_zero]
    simp only [kap, D, Gam, pow_zero, Nat.sub_self, mul_one]
    omega
  | L + 1, U, ρ, n, ξ, j, b, h, hj, hb, hc => by
    obtain ⟨-, -, h3⟩ := Q_sub m L U ρ n ξ h
    rw [contam_succ] at hc
    have key : ∀ s ∈ cset m L U ρ ξ j, kap m L ≤
        (phase m L (qU m L U ρ ξ) (ρ.drop (qOffs m L U ρ ξ s))).dem j b * D L * Gam L j.val := by
      intro s hs
      rw [mem_cset] at hs
      obtain ⟨ns, hns, -, hle⟩ := sub_in m L U ρ n ξ h s hs.1
      exact lem57 L _ _ ns _ j b hns (by omega)
        (fun t ht => by simp only [sh]; exact hb _ (by omega)) hs.2
    have hsum : (cset m L U ρ ξ j).card * kap m L ≤
        (phase m (L + 1) U ρ).dem j b * (D L * Gam L j.val) := by
      calc (cset m L U ρ ξ j).card * kap m L = ∑ s ∈ cset m L U ρ ξ j, kap m L := by simp
        _ ≤ ∑ s ∈ cset m L U ρ ξ j,
            (phase m L (qU m L U ρ ξ) (ρ.drop (qOffs m L U ρ ξ s))).dem j b * D L * Gam L j.val :=
          Finset.sum_le_sum key
        _ = (∑ s ∈ cset m L U ρ ξ j,
            (phase m L (qU m L U ρ ξ) (ρ.drop (qOffs m L U ρ ξ s))).dem j b) * (D L * Gam L j.val) := by
          rw [Finset.sum_mul]; simp only [mul_assoc]
        _ ≤ (∑ s ∈ Finset.range (m L),
            (phase m L (qU m L U ρ ξ) (ρ.drop (qOffs m L U ρ ξ s))).dem j b) * (D L * Gam L j.val) :=
          Nat.mul_le_mul_right _ (Finset.sum_le_sum_of_subset (cset_sub m L U ρ ξ _))
        _ ≤ _ := Nat.mul_le_mul_right _ (h3 j b)
    simp only [kap, Gam]
    calc D (L + 1) * m L * kap m L
        ≤ D (L + 1) * (2 ^ (j.val + 2 - L) * (cset m L U ρ ξ j).card) * kap m L := by gcongr
      _ = D (L + 1) * 2 ^ (j.val + 2 - L) * ((cset m L U ρ ξ j).card * kap m L) := by ring
      _ ≤ D (L + 1) * 2 ^ (j.val + 2 - L) *
          ((phase m (L + 1) U ρ).dem j b * (D L * Gam L j.val)) := by gcongr
      _ = _ := by ring

/-- In the explore case the hard multiphase is the explore part. -/
theorem Q_explore (L : ℕ) (U : PSet M) (ρ : List (Config M)) (n : ℕ) (ξ : ℕ → Config M)
    (h : (phase m (L + 1) U ρ).stop = some n) (hb : ξ 0 (srv (L + 1)) ∉ Sc m L U ρ)
    (j : Fin k) (b : M j) :
    ∑ s ∈ Finset.range (m L), (phase m L (qU m L U ρ ξ) (ρ.drop (qOffs m L U ρ ξ s))).dem j b =
      (Ex m L U ρ).dem j b := by
  obtain ⟨hE, -, -, -⟩ := phase_succ_some m L U ρ n h
  have e1 : qOff m L U ρ ξ = 0 := if_neg hb
  have e2 : qU m L U ρ ξ = U := if_neg hb
  obtain ⟨-, -, i3⟩ := iter_some _ _ _ _ hE
  have i3' : (Ex m L U ρ).dem = ∑ s ∈ Finset.range (m L),
      (phase m L U (ρ.drop (off (phase m L U) ρ s))).dem := i3
  simp only [qOffs, e1, e2, List.drop_zero, zero_add]
  rw [i3', Finset.sum_apply, Finsupp.finsetSum_apply]

/-- Lemma 5.8: if server `ℓ` stays still, at most `m/16` restrictions are `ℓ`-contaminated. -/
theorem lem58 (L : ℕ) (hL : L + 1 < k) (hm : ∀ i, i ≤ L → 1 ≤ m i) (U : PSet M)
    (ρ : List (Config M)) (n : ℕ) (ξ : ℕ → Config M) (hU : Low (L + 1) U)
    (h : (phase m (L + 1) U ρ).stop = some n)
    (hst : ∀ t ≤ n, ξ t (srv (L + 1)) = ξ 0 (srv (L + 1))) :
    16 * (cset m L U ρ ξ (srv (L + 1))).card ≤ m L := by
  have hkap : 0 < kap m L := kap_pos m L (fun i hi => hm i (by omega))
  have hjv : (srv (k := k) (L + 1)).val = L + 1 := srv_val _ hL
  set b := ξ 0 (srv (L + 1)) with hbdef
  have key : ∀ s ∈ cset m L U ρ ξ (srv (L + 1)), kap m L ≤
      (phase m L (qU m L U ρ ξ) (ρ.drop (qOffs m L U ρ ξ s))).dem (srv (L + 1)) b * D L *
        Gam L (L + 1) := by
    intro s hs
    rw [mem_cset] at hs
    obtain ⟨ns, hns, -, hle⟩ := sub_in m L U ρ n ξ h s hs.1
    have := lem57 m L _ _ ns _ (srv (L + 1)) b hns (by omega)
      (fun t ht => by simp only [sh]; exact hst _ (by omega)) hs.2
    rwa [hjv] at this
  by_cases hb : b ∈ Sc m L U ρ
  · have e2 : qU m L U ρ ξ = Function.update U (srv (L + 1)) (some b) := if_pos hb
    have : cset m L U ρ ξ (srv (L + 1)) = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro s hs
      have hk := key s hs
      rw [mem_cset] at hs
      obtain ⟨ns, hns, -, -⟩ := sub_in m L U ρ n ξ h s hs.1
      have hz := phase_vanish m L (by omega) _ _ ns (qU_low m L hL U ρ ξ hU) hns (srv (L + 1)) b
        (by rw [e2, Function.update_self])
      rw [hz] at hk
      simp at hk
      omega
    rw [this]; simp
  · have hQ := Q_explore m L U ρ n ξ h hb (srv (L + 1)) b
    obtain ⟨hE, -, -, -⟩ := phase_succ_some m L U ρ n h
    set V0 := (Ex m L U ρ).dem (srv (L + 1)) with hV0
    -- contaminated phases give demand at `b`
    have h1 : (cset m L U ρ ξ (srv (L + 1))).card * kap m L ≤ V0 b * (D L * Gam L (L + 1)) := by
      calc (cset m L U ρ ξ (srv (L + 1))).card * kap m L
          = ∑ s ∈ cset m L U ρ ξ (srv (L + 1)), kap m L := by simp
        _ ≤ ∑ s ∈ cset m L U ρ ξ (srv (L + 1)),
            (phase m L (qU m L U ρ ξ) (ρ.drop (qOffs m L U ρ ξ s))).dem (srv (L + 1)) b * D L *
              Gam L (L + 1) := Finset.sum_le_sum key
        _ = (∑ s ∈ cset m L U ρ ξ (srv (L + 1)),
            (phase m L (qU m L U ρ ξ) (ρ.drop (qOffs m L U ρ ξ s))).dem (srv (L + 1)) b) *
              (D L * Gam L (L + 1)) := by
          rw [Finset.sum_mul]; simp only [mul_assoc]
        _ ≤ (∑ s ∈ Finset.range (m L),
            (phase m L (qU m L U ρ ξ) (ρ.drop (qOffs m L U ρ ξ s))).dem (srv (L + 1)) b) *
              (D L * Gam L (L + 1)) :=
          Nat.mul_le_mul_right _ (Finset.sum_le_sum_of_subset (cset_sub m L U ρ ξ _))
        _ = _ := by rw [hQ]
    -- the critical set is full and dominates `b`
    obtain ⟨hcard, hdom⟩ := crit_full V0 (D (L + 1) - 1) b hb
    have hD := D_pos (L + 1)
    have h2 : D (L + 1) * V0 b ≤ m L * kap m L := by
      classical
      have hn := iter_nrm m L (phase_nrm m L) U ρ _ hE (srv (L + 1))
      have hs := sum_le_nrm V0 (insert b (Sc m L U ρ))
      rw [Finset.sum_insert hb] at hs
      have hs2 : ∑ p ∈ Sc m L U ρ, V0 b ≤ ∑ p ∈ Sc m L U ρ, V0 p := Finset.sum_le_sum hdom
      rw [Finset.sum_const, smul_eq_mul] at hs2
      have hc : (Sc m L U ρ).card = D (L + 1) - 1 := hcard
      rw [hc] at hs2
      have hn' : nrm V0 ≤ m L * kap m L := hn
      obtain ⟨d, hd⟩ : ∃ d, D (L + 1) = d + 1 := ⟨D (L + 1) - 1, by omega⟩
      rw [hd] at hs2 ⊢
      simp only [add_tsub_cancel_right] at hs2
      nlinarith
    have h56 := lem56 L
    -- combine
    set c := (cset m L U ρ ξ (srv (L + 1))).card
    have h3 : 16 * c * kap m L * D (L + 1) ≤ m L * kap m L * D (L + 1) := by
      calc 16 * c * kap m L * D (L + 1) = 16 * (c * kap m L) * D (L + 1) := by ring
        _ ≤ 16 * (V0 b * (D L * Gam L (L + 1))) * D (L + 1) := by gcongr
        _ = (D (L + 1) * V0 b) * (16 * D L * Gam L (L + 1)) := by ring
        _ ≤ (m L * kap m L) * D (L + 1) := Nat.mul_le_mul h2 h56
    have hpos : 0 < kap m L * D (L + 1) := Nat.mul_pos hkap hD
    have : 16 * c * (kap m L * D (L + 1)) ≤ m L * (kap m L * D (L + 1)) := by
      simpa only [mul_assoc] using h3
    exact Nat.le_of_mul_le_mul_right this hpos

end GeneralizedUniformServer.Dev.WB.PartL
end
end

section
set_option autoImplicit false
open scoped NNReal
noncomputable section
namespace GeneralizedUniformServer.Dev.WB.PartL
open GeneralizedUniformServer.UnitWeights GeneralizedUniformServer.UnitWeights.Supplement
open GeneralizedUniformServer.Dev.WB
variable {k : ℕ} {M : Fin k → Type*}
variable [NeZero k] (m : ℕ → ℕ) (v : Fin k → ℝ≥0)
/-- Fewer than `3m/16` phases of the hard multiphase are not good (proof of Lemma 5.9). -/
theorem bad_bound (hv : Normalized v m) (L : ℕ) (hL : L + 1 < k) (U : PSet M)
    (ρ : List (Config M)) (n : ℕ) (ξ : ℕ → Config M) (hU : Low (L + 1) U)
    (h : (phase m (L + 1) U ρ).stop = some n)
    (hst : ∀ t ≤ n, ∀ j : Fin k, L + 1 ≤ j.val → ξ t j = ξ 0 j)
    (hnc : ∀ j : Fin k, L + 1 < j.val → ¬ contam m (L + 1) U ρ ξ j) :
    16 * (badS m L U ρ ξ).card ≤ 3 * m L := by
  classical
  have hsub : badS m L U ρ ξ ⊆ (Finset.univ.filter fun j : Fin k => L + 1 ≤ j.val).biUnion
      (fun j => cset m L U ρ ξ j) := by
    intro s hs
    rw [badS, Finset.mem_filter] at hs
    obtain ⟨hs1, hs2⟩ := hs
    simp only [good, not_forall, not_not] at hs2
    obtain ⟨j, hj, hc⟩ := hs2
    rw [Finset.mem_biUnion]
    exact ⟨j, Finset.mem_filter.2 ⟨Finset.mem_univ _, hj⟩,
      (mem_cset m L U ρ ξ j s).2 ⟨Finset.mem_range.1 hs1, hc⟩⟩
  have hcard := (Finset.card_le_card hsub).trans Finset.card_biUnion_le
  rw [Finset.sum_filter] at hcard
  have h58 := lem58 m L hL (fun i hi => by have := (hv.2 i (by omega)).1; omega) U ρ n ξ hU h
    (fun t ht => hst t ht _ (by rw [srv_val _ hL]))
  set mm : ℝ := (m L : ℝ) with hmm
  have hterm : ∀ j : Fin k, (if L + 1 ≤ j.val then ((cset m L U ρ ξ j).card : ℝ) else 0) ≤
      (if j.val = L + 1 then mm / 16 else 0) +
        mm * (if L + 1 < j.val then (1 / 2 : ℝ) ^ (j.val + 2 - L) else 0) := by
    intro j
    by_cases h1 : j.val = L + 1
    · have hj : j = srv (L + 1) := Fin.ext (by rw [srv_val _ hL]; exact h1)
      rw [if_pos (by omega), if_pos h1, if_neg (by omega), mul_zero, add_zero]
      subst hj
      have : (16 : ℝ) * (cset m L U ρ ξ (srv (L + 1))).card ≤ mm := by
        rw [hmm]; exact_mod_cast h58
      linarith
    · by_cases h2 : L + 1 < j.val
      · rw [if_pos (by omega), if_neg h1, if_pos h2, zero_add]
        have := hnc j h2
        rw [contam_succ] at this
        push Not at this
        have h3 : ((2 : ℝ) ^ (j.val + 2 - L)) * (cset m L U ρ ξ j).card ≤ mm := by
          rw [hmm]; exact_mod_cast this.le
        have hpos : (0 : ℝ) < 2 ^ (j.val + 2 - L) := by positivity
        rw [div_pow, one_pow, mul_one_div, le_div_iff₀ hpos]
        linarith
      · rw [if_neg (by omega), if_neg h1, if_neg h2]
        simp
  have hcR : ((badS m L U ρ ξ).card : ℝ) ≤
      ∑ j : Fin k, (if L + 1 ≤ j.val then ((cset m L U ρ ξ j).card : ℝ) else 0) := by
    have := (Nat.cast_le (α := ℝ)).2 hcard
    push_cast at this
    exact this
  have hsum : ((badS m L U ρ ξ).card : ℝ) ≤ mm / 16 + mm * (1 / 8) := by
    calc ((badS m L U ρ ξ).card : ℝ)
        ≤ ∑ j : Fin k, ((if j.val = L + 1 then mm / 16 else 0) +
            mm * (if L + 1 < j.val then (1 / 2 : ℝ) ^ (j.val + 2 - L) else 0)) :=
          hcR.trans (Finset.sum_le_sum fun j _ => hterm j)
      _ = ∑ t ∈ Finset.range k, ((if t = L + 1 then mm / 16 else 0) +
            mm * (if L + 1 < t then (1 / 2 : ℝ) ^ (t + 2 - L) else 0)) :=
          Fin.sum_univ_eq_sum_range (fun t => (if t = L + 1 then mm / 16 else 0) +
            mm * (if L + 1 < t then (1 / 2 : ℝ) ^ (t + 2 - L) else 0)) k
      _ = ∑ t ∈ Finset.range k, (if t = L + 1 then mm / 16 else 0) +
            mm * ∑ t ∈ Finset.range k, (if L + 1 < t then (1 / 2 : ℝ) ^ (t + 2 - L) else 0) := by
          rw [Finset.sum_add_distrib, Finset.mul_sum]
      _ ≤ mm / 16 + mm * (1 / 8) := by
          have hmm0 : 0 ≤ mm := by rw [hmm]; positivity
          gcongr
          · rw [Finset.sum_ite_eq']
            split_ifs
            · exact le_rfl
            · positivity
          · exact geom_bound L k
  have : (16 : ℝ) * (badS m L U ρ ξ).card ≤ 3 * mm := by linarith
  rw [hmm] at this
  exact_mod_cast this

/-- Witness of a good level-0 phase, at index `a + w`: server `0` serves it. -/
theorem factA (hk : 1 < k) (ρ : List (Config M)) (n : ℕ) (ξ : ℕ → Config M) (hsol : Sol ρ n ξ)
    (hst : ∀ t ≤ n, ∀ j : Fin k, 1 ≤ j.val → ξ t j = ξ 0 j) (a w : ℕ) (rw : Config M)
    (hρ : ρ[a + w]? = some rw) (hwn : a + w < n)
    (hgood : ∀ j : Fin k, 1 ≤ j.val → ξ a j ≠ rw j) : ξ (a + w + 1) (srv 0) = rw (srv 0) := by
  obtain ⟨j, hj⟩ := hsol (a + w) hwn rw hρ
  by_cases h1 : 1 ≤ j.val
  · exfalso
    apply hgood j h1
    rw [hst a (by omega) j h1, ← hst (a + w + 1) (by omega) j h1]
    exact hj
  · have : j = srv 0 := Fin.ext (by rw [srv_val 0 (by omega)]; omega)
    rw [← this]; exact hj

theorem good0_ne (U' : PSet M) (ρ' : List (Config M)) (ξ' : ℕ → Config M) (j : Fin k)
    (rw : Config M) (hd : (phase0 U' ρ').dem = fun j => Finsupp.single (rw j) 1)
    (hnc : ¬ contam m 0 U' ρ' ξ' j) : ξ' 0 j ≠ rw j := by
  intro e
  apply hnc
  simp only [contam, hd, e, Finsupp.single_eq_same]
  norm_num

/-- Count of consecutive pairs of good phases. -/
theorem pairs_count (mm : ℕ) (B : Finset ℕ) (P : ℕ → Prop) [DecidablePred P]
    (hB : ∀ s < mm, ¬ P s → s ∈ B) :
    mm - 1 ≤ ((Finset.range (mm - 1)).filter fun s => P s ∧ P (s + 1)).card + 2 * B.card := by
  classical
  have hsub : Finset.range (mm - 1) ⊆ ((Finset.range (mm - 1)).filter fun s => P s ∧ P (s + 1)) ∪
      (B ∪ B.image (· - 1)) := by
    intro s hs
    rw [Finset.mem_range] at hs
    by_cases h1 : P s ∧ P (s + 1)
    · exact Finset.mem_union_left _ (Finset.mem_filter.2 ⟨Finset.mem_range.2 hs, h1⟩)
    · rw [not_and_or] at h1
      rcases h1 with h1 | h1
      · exact Finset.mem_union_right _ (Finset.mem_union_left _ (hB s (by omega) h1))
      · exact Finset.mem_union_right _ (Finset.mem_union_right _
          (Finset.mem_image.2 ⟨s + 1, hB (s + 1) (by omega) h1, by simp⟩))
  have := Finset.card_le_card hsub
  rw [Finset.card_range] at this
  have h2 := Finset.card_union_le ((Finset.range (mm - 1)).filter fun s => P s ∧ P (s + 1))
    (B ∪ B.image (· - 1))
  have h3 := Finset.card_union_le B (B.image (· - 1))
  have h4 : (B.image (· - 1)).card ≤ B.card := Finset.card_image_le
  omega

/-- Lemma 5.9 for `ℓ = 2` when servers `2, …, k` stay still. -/
theorem lem59_base (hv : Normalized v m) (hk : 1 < k) (U : PSet M) (ρ : List (Config M)) (n : ℕ)
    (ξ : ℕ → Config M) (hU : Low 1 U) (h : (phase m (0 + 1) U ρ).stop = some n) (hsol : Sol ρ n ξ)
    (hst : ∀ t ≤ n, ∀ j : Fin k, 0 + 1 ≤ j.val → ξ t j = ξ 0 j)
    (hnc : ∀ j : Fin k, 0 + 1 < j.val → ¬ contam m (0 + 1) U ρ ξ j) :
    (v (srv (0 + 1)) : ℝ) / 2 ^ (0 + 2) ≤ cI v ξ 0 n := by
  classical
  have hm2 : 2 ≤ m 0 := (hv.2 0 hk).1
  set mm := m 0 with hmmdef
  have hQU0 : qU m 0 U ρ ξ (srv 0) = none :=
    qU_low m 0 hk U ρ ξ hU (srv 0) (by rw [srv_val 0 (by omega)])
  -- the pair bound
  have hpair : ∀ s, s + 1 < mm → good m 0 U ρ ξ s → good m 0 U ρ ξ (s + 1) →
      (v (srv 0) : ℝ) ≤ cI v ξ (qOffs m 0 U ρ ξ s + 1) (qOffs m 0 U ρ ξ (s + 1) + 1) := by
    intro s hs gs gs1
    obtain ⟨ns, hns, hstep, hle⟩ := sub_in m 0 U ρ n ξ h s (by omega)
    rw [phase_zero] at hns
    obtain ⟨w, hw, rw, hrw, -, -, ⟨r', hr', hr'n⟩, hd⟩ := phase0_some _ _ _ hns
    obtain ⟨ns', hns', -, hle'⟩ := sub_in m 0 U ρ n ξ h (s + 1) (by omega)
    rw [phase_zero] at hns'
    obtain ⟨w', hw', rw', hrw', -, hpre', -, hd'⟩ := phase0_some _ _ _ hns'
    rw [List.getElem?_drop] at hrw hr' hrw'
    have hr'g : ρ[qOffs m 0 U ρ ξ (s + 1)]? = some r' := by rw [hstep]; exact hr'
    have hr'notU : ¬ Sat (qU m 0 U ρ ξ) r' := by
      rintro ⟨j, hj⟩
      apply hr'n
      refine ⟨j, ?_⟩
      have hjne : j ≠ srv 0 := by
        rintro rfl
        rw [hQU0] at hj
        cases hj
      rw [Function.update_of_ne hjne]
      exact hj
    have hw'0 : w' = 0 := by
      by_contra hne
      exact hr'notU (hpre' 0 (by omega) r' (by rw [List.getElem?_drop, add_zero]; exact hr'g))
    subst hw'0
    have hrw'r : rw' = r' := by
      rw [add_zero] at hrw'
      have := hrw'.symm.trans hr'g
      exact Option.some.inj this
    subst hrw'r
    have hdiff : rw' (srv 0) ≠ rw (srv 0) := fun e => hr'n ⟨srv 0, by rw [Function.update_self, e]⟩
    have A1 := factA hk ρ n ξ hsol hst (qOffs m 0 U ρ ξ s) w rw hrw (by omega)
      (fun j hj => by
        have := good0_ne m _ _ _ j rw hd (gs j hj)
        simpa [sh] using this)
    have A2 := factA hk ρ n ξ hsol hst (qOffs m 0 U ρ ξ (s + 1)) 0 rw' hrw' (by omega)
      (fun j hj => by
        have := good0_ne m _ _ _ j rw' hd' (gs1 j hj)
        simpa [sh] using this)
    have hmv : ξ (qOffs m 0 U ρ ξ s + w + 1) (srv 0) ≠ ξ (qOffs m 0 U ρ ξ (s + 1) + 0 + 1) (srv 0) := by
      rw [A1, A2]; exact fun e => hdiff e.symm
    calc (v (srv 0) : ℝ) ≤ cI v ξ (qOffs m 0 U ρ ξ s + w + 1) (qOffs m 0 U ρ ξ (s + 1) + 0 + 1) :=
          move_cost v ξ (srv 0) _ _ (by omega) hmv
      _ ≤ cI v ξ (qOffs m 0 U ρ ξ s + 1) (qOffs m 0 U ρ ξ (s + 1) + 1) := cI_mono v ξ (by omega) (by omega)
  -- consecutive intervals
  have hmono : ∀ s < mm - 1, qOffs m 0 U ρ ξ s + 1 ≤ qOffs m 0 U ρ ξ (s + 1) + 1 := by
    intro s hs
    obtain ⟨ns, -, hstep, -⟩ := sub_in m 0 U ρ n ξ h s (by omega)
    omega
  obtain ⟨hc1, -⟩ := cI_consec v ξ (fun s => qOffs m 0 U ρ ξ s + 1) (mm - 1) hmono
  have hlast : qOffs m 0 U ρ ξ (mm - 1) + 1 ≤ n := by
    obtain ⟨ns, hns, hstep, hle⟩ := sub_in m 0 U ρ n ξ h (mm - 1) (by omega)
    rw [phase_zero] at hns
    obtain ⟨w, hw, -⟩ := phase0_some _ _ _ hns
    omega
  set GP := (Finset.range (mm - 1)).filter fun s => good m 0 U ρ ξ s ∧ good m 0 U ρ ξ (s + 1)
  have hcost : (GP.card : ℝ) * v (srv 0) ≤ cI v ξ 0 n := by
    calc (GP.card : ℝ) * v (srv 0) = ∑ s ∈ GP, (v (srv 0) : ℝ) := by simp
      _ ≤ ∑ s ∈ GP, cI v ξ (qOffs m 0 U ρ ξ s + 1) (qOffs m 0 U ρ ξ (s + 1) + 1) := by
          refine Finset.sum_le_sum fun s hs => ?_
          rw [Finset.mem_filter, Finset.mem_range] at hs
          exact hpair s (by omega) hs.2.1 hs.2.2
      _ ≤ ∑ s ∈ Finset.range (mm - 1), cI v ξ (qOffs m 0 U ρ ξ s + 1) (qOffs m 0 U ρ ξ (s + 1) + 1) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (fun _ _ _ => cI_nonneg v ξ _ _)
      _ = cI v ξ (qOffs m 0 U ρ ξ 0 + 1) (qOffs m 0 U ρ ξ (mm - 1) + 1) := hc1
      _ ≤ cI v ξ 0 n := cI_mono v ξ (by omega) hlast
  have hbad := bad_bound m v hv 0 hk U ρ n ξ hU h hst hnc
  have hcnt : mm - 1 ≤ GP.card + 2 * (badS m 0 U ρ ξ).card := pairs_count mm (badS m 0 U ρ ξ) (good m 0 U ρ ξ) (fun s hs hg => by
    rw [badS, Finset.mem_filter, Finset.mem_range]; exact ⟨hs, hg⟩)
  have hfin : mm ≤ 4 * GP.card := by
    have h8 : 8 * (mm - 1) ≤ 8 * GP.card + 16 * (badS m 0 U ρ ξ).card := by omega
    rcases Nat.lt_or_ge mm 3 with h3 | h3
    · have : (badS m 0 U ρ ξ).card = 0 := by omega
      omega
    · omega
  have hv1 := v_succ m v hv 0 hk
  rw [zero_add] at hv1 ⊢
  rw [hv1]
  have hfinR : (mm : ℝ) ≤ 4 * GP.card := by exact_mod_cast hfin
  have hv0 : (0 : ℝ) ≤ v (srv 0) := NNReal.coe_nonneg _
  push_cast
  nlinarith

/-- If some server `≥ ℓ` moves, the cost is at least `v_ℓ`. -/
theorem lem59_move (hv : Normalized v m) (L : ℕ) (hL : L + 1 < k) (n : ℕ) (ξ : ℕ → Config M)
    (hmove : ∃ t < n, ∃ j : Fin k, L + 1 ≤ j.val ∧ ξ t j ≠ ξ (t + 1) j) :
    (v (srv (L + 1)) : ℝ) / 2 ^ (L + 2) ≤ cI v ξ 0 n := by
  obtain ⟨t, ht, j, hj, hne⟩ := hmove
  calc (v (srv (L + 1)) : ℝ) / 2 ^ (L + 2) ≤ v (srv (L + 1)) :=
        div_le_self (NNReal.coe_nonneg _) (one_le_pow₀ (by norm_num))
    _ ≤ v j := by exact_mod_cast v_mono m v hv (L + 1) hL j hj
    _ ≤ cI v ξ t (t + 1) := move_cost v ξ j t (t + 1) (by omega) hne
    _ ≤ cI v ξ 0 n := cI_mono v ξ (by omega) (by omega)

omit [NeZero k] in
theorem still_of_not_move (L n : ℕ) (ξ : ℕ → Config M)
    (hmove : ¬ ∃ t < n, ∃ j : Fin k, L + 1 ≤ j.val ∧ ξ t j ≠ ξ (t + 1) j) :
    ∀ t ≤ n, ∀ j : Fin k, L + 1 ≤ j.val → ξ t j = ξ 0 j := by
  push Not at hmove
  intro t ht j hj
  induction t with
  | zero => rfl
  | succ t ih => rw [← hmove t (by omega) j hj]; exact ih (by omega)

/-- **Lemma 5.9.** A solution that is not contaminated for a completed `(ℓ, U)`-phase,
`ℓ ≥ 2`, costs at least `v_ℓ / 2^ℓ`. -/
theorem lem59 (hv : Normalized v m) : ∀ L : ℕ, L + 1 < k → ∀ (U : PSet M) (ρ : List (Config M))
    (n : ℕ) (ξ : ℕ → Config M), Low (L + 1) U → (phase m (L + 1) U ρ).stop = some n →
    Sol ρ n ξ → (∀ j : Fin k, L + 1 < j.val → ¬ contam m (L + 1) U ρ ξ j) →
    (v (srv (L + 1)) : ℝ) / 2 ^ (L + 2) ≤ cI v ξ 0 n := by
  intro L
  induction L with
  | zero =>
    intro hL U ρ n ξ hU h hsol hnc
    by_cases hmove : ∃ t < n, ∃ j : Fin k, 0 + 1 ≤ j.val ∧ ξ t j ≠ ξ (t + 1) j
    · exact lem59_move m v hv 0 hL n ξ hmove
    · exact lem59_base m v hv (by omega) U ρ n ξ hU h hsol (still_of_not_move 0 n ξ hmove) hnc
  | succ L ih =>
    intro hL U ρ n ξ hU h hsol hnc
    by_cases hmove : ∃ t < n, ∃ j : Fin k, L + 1 + 1 ≤ j.val ∧ ξ t j ≠ ξ (t + 1) j
    · exact lem59_move m v hv (L + 1) hL n ξ hmove
    · have hst := still_of_not_move (L + 1) n ξ hmove
      classical
      set mm := m (L + 1) with hmmdef
      set x : ℝ := (v (srv (L + 1)) : ℝ) / 2 ^ (L + 2) with hx
      have hgood : ∀ s < mm, good m (L + 1) U ρ ξ s → x ≤ cI v ξ (qOffs m (L + 1) U ρ ξ s) (qOffs m (L + 1) U ρ ξ (s + 1)) := by
        intro s hs gs
        obtain ⟨ns, hns, hstep, hle⟩ := sub_in m (L + 1) U ρ n ξ h s hs
        have := ih (by omega) _ _ ns (sh ξ (qOffs m (L + 1) U ρ ξ s)) (qU_low m (L + 1) hL U ρ ξ hU) hns
          (sol_sh ξ ρ n (qOffs m (L + 1) U ρ ξ s) ns hsol hle) (fun j hj => gs j (by omega))
        rw [cI_sh] at this
        rw [hstep]
        exact this
      have hmono : ∀ s < mm, qOffs m (L + 1) U ρ ξ s ≤ qOffs m (L + 1) U ρ ξ (s + 1) := by
        intro s hs
        obtain ⟨ns, -, hstep, -⟩ := sub_in m (L + 1) U ρ n ξ h s hs
        omega
      obtain ⟨hc1, -⟩ := cI_consec v ξ (qOffs m (L + 1) U ρ ξ) mm hmono
      obtain ⟨-, hQle, -⟩ := Q_sub m (L + 1) U ρ n ξ h
      set G := (Finset.range mm).filter fun s => good m (L + 1) U ρ ξ s
      have hx0 : 0 ≤ x := by rw [hx]; positivity
      have hcost : (G.card : ℝ) * x ≤ cI v ξ 0 n := by
        calc (G.card : ℝ) * x = ∑ s ∈ G, x := by simp
          _ ≤ ∑ s ∈ G, cI v ξ (qOffs m (L + 1) U ρ ξ s) (qOffs m (L + 1) U ρ ξ (s + 1)) := by
              refine Finset.sum_le_sum fun s hs => ?_
              rw [Finset.mem_filter, Finset.mem_range] at hs
              exact hgood s hs.1 hs.2
          _ ≤ ∑ s ∈ Finset.range mm, cI v ξ (qOffs m (L + 1) U ρ ξ s) (qOffs m (L + 1) U ρ ξ (s + 1)) :=
              Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
                (fun _ _ _ => cI_nonneg v ξ _ _)
          _ = cI v ξ (qOffs m (L + 1) U ρ ξ 0) (qOffs m (L + 1) U ρ ξ mm) := hc1
          _ ≤ cI v ξ 0 n := cI_mono v ξ (by omega) hQle
      have hbad : 16 * (badS m (L + 1) U ρ ξ).card ≤ 3 * mm :=
        bad_bound m v hv (L + 1) hL U ρ n ξ hU h hst hnc
      have hsplit : G.card + (badS m (L + 1) U ρ ξ).card = mm := by
        have := Finset.card_filter_add_card_filter_not
          (s := Finset.range mm) (fun s => good m (L + 1) U ρ ξ s)
        rw [Finset.card_range] at this
        exact this
      have hfin : mm ≤ 2 * G.card := by omega
      have hv1 := v_succ m v hv (L + 1) hL
      rw [hv1]
      have hfinR : (mm : ℝ) ≤ 2 * G.card := by exact_mod_cast hfin
      have e : ((m (L + 1) * v (srv (L + 1)) : ℝ≥0) : ℝ) / 2 ^ (L + 1 + 2) = mm * x / 2 := by
        rw [hx, hmmdef]; push_cast; ring
      rw [e]
      nlinarith

/-- **Corollary 5.10.** Every solution for a completed `(k, ∅)`-phase costs `≥ v_k / 2^k`. -/
theorem cor510 (hk : 2 ≤ k) (hv : Normalized v m) (ρ : List (Config M)) (n : ℕ)
    (ξ : ℕ → Config M) (h : (phase m (k - 1) (fun _ => none) ρ).stop = some n)
    (hsol : Sol ρ n ξ) : (v (srv (k - 1)) : ℝ) / 2 ^ k ≤ cI v ξ 0 n := by
  obtain ⟨L, hL⟩ : ∃ L, k - 1 = L + 1 := ⟨k - 2, by omega⟩
  rw [hL] at h ⊢
  have e : (2 : ℝ) ^ k = 2 ^ (L + 2) := by congr 1; omega
  rw [e]
  exact lem59 m v hv L (by omega) _ ρ n ξ (fun _ _ => rfl) h hsol
    (fun j hj => absurd j.isLt (by omega))

end GeneralizedUniformServer.Dev.WB.PartL
end
end

section
set_option autoImplicit false
open scoped NNReal
noncomputable section
namespace GeneralizedUniformServer.Dev.WB.PartL
open GeneralizedUniformServer.UnitWeights GeneralizedUniformServer.UnitWeights.Supplement
open GeneralizedUniformServer.Dev.WB
variable {k : ℕ} {M : Fin k → Type*}
/-! ## The sum over the phase calls -/
theorem ncallsAux_nil (f : List (Config M) → PR M) : ∀ fuel, ncallsAux f fuel [] = 0
  | 0 => rfl
  | _ + 1 => rfl

theorem count_bound (v : Fin k → ℝ≥0) (f : List (Config M) → PR M) (c : ℝ)
    (hc : ∀ (ρ : List (Config M)) (n : ℕ) (ξ : ℕ → Config M), (f ρ).stop = some n → Sol ρ n ξ →
      c ≤ cI v ξ 0 n) (hc0 : 0 ≤ c) :
    ∀ (fuel : ℕ) (ρ : List (Config M)) (ξ : ℕ → Config M), Sol ρ ρ.length ξ →
      ((ncallsAux f fuel ρ : ℝ) - 1) * c ≤ cI v ξ 0 ρ.length
  | 0, ρ, ξ, _ => by
    simp only [ncallsAux, Nat.cast_zero]
    nlinarith [cI_nonneg v ξ 0 ρ.length]
  | fuel + 1, [], ξ, _ => by
    simp only [ncallsAux, Nat.cast_zero, List.length_nil]
    nlinarith [cI_nonneg v ξ 0 0]
  | fuel + 1, r :: ρ, ξ, hsol => by
    cases hs : (f (r :: ρ)).stop with
    | none =>
      simp only [ncallsAux, hs, Nat.cast_one, sub_self, zero_mul]
      exact cI_nonneg v ξ _ _
    | some n =>
      simp only [ncallsAux, hs]
      have hsoln : Sol (r :: ρ) n ξ := by
        intro t ht r' hr'
        have hlt : t < (r :: ρ).length := by
          by_contra hge
          rw [List.getElem?_eq_none (by omega)] at hr'
          cases hr'
        exact hsol t hlt r' hr'
      have h1 := hc _ n ξ hs hsoln
      by_cases hn : n ≤ (r :: ρ).length
      · have hsol' : Sol ((r :: ρ).drop n) ((r :: ρ).drop n).length (sh ξ n) := by
          rw [List.length_drop]
          exact sol_sh ξ _ _ n _ hsol (by omega)
        have ih := count_bound v f c hc hc0 fuel ((r :: ρ).drop n) (sh ξ n) hsol'
        rw [cI_sh, List.length_drop, show n + ((r :: ρ).length - n) = (r :: ρ).length by omega]
          at ih
        have hadd := cI_add v ξ (Nat.zero_le n) hn
        push_cast
        nlinarith
      · rw [List.drop_eq_nil_of_le (by omega), ncallsAux_nil]
        simp only [add_zero, Nat.cast_one, sub_self, zero_mul]
        exact cI_nonneg v ξ _ _

/-- **Part L** (Corollary 5.10 summed over the completed phases). Every offline solution
pays at least `v_k / 2^k` per completed `(k, ∅)`-phase. -/
theorem offline_bound [NeZero k] (hk : 2 ≤ k) (v : Fin k → ℝ≥0) (m : ℕ → ℕ)
    (hv : Normalized v m) (ρ : List (Config M)) (o : Fin (ρ.length + 1) → Config M)
    (ho : IsOfflineSolution ρ o) :
    ((ncalls m ρ : ℝ) - 1) * ((v (srv (k - 1)) : ℝ) / 2 ^ k) ≤ (wOfflineCost v ρ o : ℝ) := by
  set ξ : ℕ → Config M := fun t => o ⟨min t ρ.length, by omega⟩ with hξ
  have hsol : Sol ρ ρ.length ξ := by
    intro t ht r hr
    have e : ρ[t] = r := by
      rw [List.getElem?_eq_getElem ht] at hr; exact Option.some.inj hr
    have := ho ⟨t, ht⟩
    rw [← e]
    have e2 : ξ (t + 1) = o (Fin.succ ⟨t, ht⟩) := by
      simp only [hξ]; congr 1; ext; simp; omega
    rw [e2]
    exact this
  have hcost : (wOfflineCost v ρ o : ℝ) = cI v ξ 0 ρ.length := by
    unfold wOfflineCost cI
    rw [NNReal.coe_sum, ← Finset.range_eq_Ico]
    rw [← Fin.sum_univ_eq_sum_range (fun t => (wdist v (ξ t) (ξ (t + 1)) : ℝ)) ρ.length]
    refine Finset.sum_congr rfl fun s _ => ?_
    have e1 : ξ s = o s.castSucc := by
      simp only [hξ]; congr 1; ext; simp
    have e2 : ξ (s + 1) = o s.succ := by
      simp only [hξ]; congr 1; ext; simp
    rw [e1, e2]
  rw [hcost]
  exact count_bound v _ _ (fun ρ' n ξ' h hs => cor510 m v hk hv ρ' n ξ' h hs) (by positivity)
    ρ.length ρ ξ hsol

end GeneralizedUniformServer.Dev.WB.PartL
end
end

section
open scoped NNReal
noncomputable section
namespace GeneralizedUniformServer.Dev.WB
open GeneralizedUniformServer.UnitWeights GeneralizedUniformServer.UnitWeights.Supplement
variable {k : ℕ} {M : Fin k → Type*}
alias offline_bound := GeneralizedUniformServer.Dev.WB.PartL.offline_bound

end GeneralizedUniformServer.Dev.WB
end
end

section
set_option autoImplicit false
open scoped NNReal
noncomputable section
namespace GeneralizedUniformServer.Dev.WB.PartF
open GeneralizedUniformServer.UnitWeights GeneralizedUniformServer.UnitWeights.Supplement
open GeneralizedUniformServer.Dev.WB
variable {k : ℕ} {M : Fin k → Type*}
/-! ## The main case -/
theorem case_main [NeZero k] (hk : 2 ≤ k) (w : Fin k → ℝ≥0) (hw : Monotone w)
    (hw0 : 0 < w 0) (a : Config M) :
    ∃ A : GenOnlineAlg M (Config M),
      IsServing Serves A ∧
      ∀ ρ : List (Config M),
        genExpectedCostW w A a ρ ≤
          (20 : ENNReal) ^ k * optCostW w a ρ +
            (10 : ENNReal) ^ k *
              ((w ⟨k - 1, Nat.sub_lt (NeZero.pos k) Nat.one_pos⟩ : ℝ≥0) : ENNReal) := by
  set W := wN w with hWdef
  have hW0 : 0 < W 0 := by
    have := wN_val w 0
    rw [Fin.val_zero] at this
    rw [hWdef, this]
    exact hw0
  have hmono : ∀ i, i + 1 < k → W i ≤ W (i + 1) := by
    intro i hi
    have e1 := wN_val w ⟨i, by omega⟩
    have e2 := wN_val w ⟨i + 1, hi⟩
    simp only at e1 e2
    rw [hWdef, e1, e2]
    exact hw (Fin.mk_le_mk.mpr (by omega))
  let v : Fin k → ℝ≥0 := fun j => vv W j
  let m : ℕ → ℕ := mm W
  have hv : Normalized v m := ⟨fun j => vv_pos W hW0 j, fun i _ => ⟨le_max_left _ _, rfl⟩⟩
  have hwv : ∀ j, w j ≤ v j := fun j => by
    rw [← wN_val w j]
    exact le_vv W hW0 j
  have hvw : ∀ j, v j ≤ 2 ^ (k - 1) * w j := fun j => by
    rw [← wN_val w j]
    calc v j ≤ 2 ^ (j : ℕ) * W j := vv_le W hW0 hmono j j.2
      _ ≤ 2 ^ (k - 1) * W j := by
          gcongr
          · norm_num
          · have := j.2; omega
  obtain ⟨F, hF⟩ := strat_bound hk v m hv a
  obtain ⟨A, hA, hc⟩ := round w a F
  have hc20 : (20 : ENNReal) ^ k ≠ 0 := by simp
  have hct : (20 : ENNReal) ^ k ≠ ⊤ := by simp
  refine ⟨A, hA, fun ρ => le_opt w a ρ _ _ _ hc20 hct fun o ho _ => ?_⟩
  have hL := offline_bound hk v m hv ρ o ho
  have hS := hF ρ
  have hsrv : srv (k - 1) = (⟨k - 1, Nat.sub_lt (NeZero.pos k) Nat.one_pos⟩ : Fin k) :=
    Fin.ext (Nat.mod_eq_of_lt (by omega))
  rw [hsrv] at hL hS
  have hoff := offline_scale w v _ hvw ρ o
  set Wk := w ⟨k - 1, Nat.sub_lt (NeZero.pos k) Nat.one_pos⟩
  have hV := hvw ⟨k - 1, Nat.sub_lt (NeZero.pos k) Nat.one_pos⟩
  refine (hc ρ).trans ?_
  rw [← ENNReal.ofNNReal_finsetSum]
  have key := arith k (by omega)
    ((∑ s ∈ Finset.range ρ.length, (F.G (ρ.take (s + 1))).cost w : ℝ≥0) : ℝ)
    (∑ s ∈ Finset.range ρ.length, ((F.G (ρ.take (s + 1))).cost v : ℝ))
    (ncalls m ρ : ℝ) (v ⟨k - 1, Nat.sub_lt (NeZero.pos k) Nat.one_pos⟩ : ℝ) (Wk : ℝ)
    (wOfflineCost v ρ o : ℝ) (wOfflineCost w ρ o : ℝ)
    (by
      push_cast
      exact Finset.sum_le_sum fun s _ => by exact_mod_cast cost_mono w v hwv _)
    hS hL (by exact_mod_cast hoff) (by exact_mod_cast hV)
  have key' : (∑ s ∈ Finset.range ρ.length, (F.G (ρ.take (s + 1))).cost w : ℝ≥0) ≤
      20 ^ k * wOfflineCost w ρ o + 10 ^ k * Wk := by
    exact_mod_cast key
  calc ((∑ s ∈ Finset.range ρ.length, (F.G (ρ.take (s + 1))).cost w : ℝ≥0) : ENNReal)
      ≤ ((20 ^ k * wOfflineCost w ρ o + 10 ^ k * Wk : ℝ≥0) : ENNReal) :=
        ENNReal.coe_le_coe.mpr key'
    _ = _ := by push_cast; rfl

/-! ## The theorem -/
theorem weighted_main {k : ℕ} [NeZero k] {M : Fin k → Type*} (w : Fin k → ℝ≥0)
    (hw : Monotone w) (a : Config M) :
    ∃ A : GenOnlineAlg M (Config M),
      IsServing Serves A ∧
      ∀ ρ : List (Config M),
        genExpectedCostW w A a ρ ≤
          (20 : ENNReal) ^ k * optCostW w a ρ +
            (10 : ENNReal) ^ k *
              ((w ⟨k - 1, Nat.sub_lt (NeZero.pos k) Nat.one_pos⟩ : ℝ≥0) : ENNReal) := by
  by_cases hw0 : w 0 = 0
  · exact case_w0 w hw0 a
  by_cases hk1 : k = 1
  · exact case_k1 hk1 w a
  have hk : 2 ≤ k := by have := NeZero.pos k; omega
  exact case_main hk w hw (pos_iff_ne_zero.mpr hw0) a

end GeneralizedUniformServer.Dev.WB.PartF
end
end

section
open scoped NNReal
noncomputable section
namespace GeneralizedUniformServer.Dev.WB
open GeneralizedUniformServer.UnitWeights GeneralizedUniformServer.UnitWeights.Supplement
variable {k : ℕ} {M : Fin k → Type*}
alias weighted_main := GeneralizedUniformServer.Dev.WB.PartF.weighted_main

end GeneralizedUniformServer.Dev.WB
end
end

section
set_option autoImplicit false
open scoped NNReal
noncomputable section
namespace GeneralizedUniformServer.Dev.WB.PartL
open GeneralizedUniformServer.UnitWeights GeneralizedUniformServer.UnitWeights.Supplement
open GeneralizedUniformServer.Dev.WB
variable {k : ℕ} {M : Fin k → Type*}

end GeneralizedUniformServer.Dev.WB.PartL
end
end

section
set_option autoImplicit false
open scoped NNReal
noncomputable section

end
end

section
open scoped NNReal
noncomputable section
open GeneralizedUniformServer
open GeneralizedUniformServer.Dev
open GeneralizedUniformServer.Dev.WB
open GeneralizedUniformServer.UnitWeights GeneralizedUniformServer.UnitWeights.Supplement
variable {k : ℕ} {M : Fin k → Type*}
theorem solution {k : ℕ} [NeZero k] {M : Fin k → Type*} (w : Fin k → ℝ≥0)
    (hw : Monotone w) (a : Config M) :
    ∃ A : GenOnlineAlg M (Config M),
      IsServing Serves A ∧
      ∀ ρ : List (Config M),
        genExpectedCostW w A a ρ ≤
          (20 : ENNReal) ^ k * optCostW w a ρ +
            (10 : ENNReal) ^ k *
              ((w ⟨k - 1, Nat.sub_lt (NeZero.pos k) Nat.one_pos⟩ : ℝ≥0) : ENNReal) := by
  exact GeneralizedUniformServer.Dev.WB.weighted_main w hw a
end
end
