-- Prove2me | solution 1 for IntLInfty.Kan.linear_horn_filler_ambient
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-10T04:02:23.134197+00:00
-- url     : https://prove2.me/submissions/0286c38c-0a4a-4b82-9bb2-6adb5f5f0e30

import Mathlib
import Definitions.Def_IntLInfty_Kan_CE
import Definitions.Def_IntLInfty_Kan_Forms
import Definitions.Def_IntLInfty_Kan_Manifold
import Definitions.Def_IntLInfty_Kan_Integ

-- slice of scratch/probe/a83e3b53.lean (closure of the decls used below), unit FILLZ

set_option autoImplicit false

namespace IntLInfty.Kan.A83D2

open MeasureTheory Filter Topology
open scoped ContDiff

variable {m : ℕ}

end IntLInfty.Kan.A83D2

namespace IntLInfty.Kan.A83

open IntLInfty.Kan

variable {L : ℕ → Type} [∀ i, AddCommGroup (L i)] [∀ i, Module ℝ (L i)]

section FormsLin

theorem convex_simplex (m : ℕ) : Convex ℝ (simplex m) := by
  intro x hx y hy a b ha hb hab
  refine ⟨fun i => ?_, ?_⟩
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact add_nonneg (mul_nonneg ha (hx.1 i)) (mul_nonneg hb (hy.1 i))
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    nlinarith [hx.2, hy.2]

theorem interior_simplex_nonempty (m : ℕ) : (interior (simplex m)).Nonempty := by
  let U : Set (Fin m → ℝ) := {t | (∀ i, 0 < t i) ∧ ∑ i, t i < 1}
  have hU : IsOpen U := by
    have h1 : IsOpen {t : Fin m → ℝ | ∀ i, 0 < t i} := by
      simpa only [Set.ofPred_forall] using
        isOpen_iInter_of_finite fun i => isOpen_lt continuous_const (continuous_apply i)
    have h2 : IsOpen {t : Fin m → ℝ | ∑ i, t i < 1} :=
      isOpen_lt (continuous_finsetSum _ fun i _ => continuous_apply i) continuous_const
    exact h1.inter h2
  have hsub : U ⊆ simplex m := fun t ht => ⟨fun i => (ht.1 i).le, ht.2.le⟩
  refine ⟨fun _ => 1 / ((m : ℝ) + 1), interior_mono hsub (hU.interior_eq.symm ▸ ?_)⟩
  refine ⟨fun i => by positivity, ?_⟩
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [mul_one_div, div_lt_one (by positivity)]
  linarith

theorem uniqueDiffOn_simplex (m : ℕ) : UniqueDiffOn ℝ (simplex m) :=
  uniqueDiffOn_convex (convex_simplex m) (interior_simplex_nonempty m)

theorem coeff_add {m : ℕ} (ω ω' : Ω m) (I : Finset (Fin m)) :
    coeff (ω + ω') I = coeff ω I + coeff ω' I := by
  funext x; simp [coeff]

theorem coeff_smul {m : ℕ} (c : ℝ) (ω : Ω m) (I : Finset (Fin m)) :
    coeff (c • ω) I = c • coeff ω I := by
  funext x; simp [coeff]

theorem jetComp_congr {m k : ℕ} {f g : (Fin m → ℝ) → ℝ} (h : Set.EqOn f g (simplex m))
    (β : Fin k → Fin m) : jetComp f k β = jetComp g k β := by
  have he : Set.EqOn (fun x => iteratedFDerivWithin ℝ k f (simplex m) x fun l => Pi.single (β l) 1)
      (fun x => iteratedFDerivWithin ℝ k g (simplex m) x fun l => Pi.single (β l) 1) (simplex m) :=
    fun x hx => by simp only [iteratedFDerivWithin_congr h hx]
  unfold jetComp
  split_ifs with h1 h2 h2
  · ext x; simp [BoundedContinuousFunction.mkOfCompact_apply, he x.2]
  · exact absurd (h1.congr he.symm) h2
  · exact absurd (h2.congr he) h1
  · rfl

theorem contOn_iter {m k r : ℕ} {f : (Fin m → ℝ) → ℝ} (hf : ContDiffOn ℝ r f (simplex m)) (hk : k ≤ r)
    (β : Fin k → Fin m) :
    ContinuousOn (fun x => iteratedFDerivWithin ℝ k f (simplex m) x fun l => Pi.single (β l) 1)
      (simplex m) :=
  (ContinuousMultilinearMap.apply ℝ (fun _ : Fin k => Fin m → ℝ) ℝ
      (fun l => Pi.single (β l) 1)).continuous.comp_continuousOn
    (hf.continuousOn_iteratedFDerivWithin (by exact_mod_cast hk) (uniqueDiffOn_simplex m))

theorem jetComp_add {m k r : ℕ} {f g : (Fin m → ℝ) → ℝ} (hf : ContDiffOn ℝ r f (simplex m))
    (hg : ContDiffOn ℝ r g (simplex m)) (hk : k ≤ r) (β : Fin k → Fin m) :
    jetComp (f + g) k β = jetComp f k β + jetComp g k β := by
  have hfk : ContDiffOn ℝ k f (simplex m) := hf.of_le (by exact_mod_cast hk)
  have hgk : ContDiffOn ℝ k g (simplex m) := hg.of_le (by exact_mod_cast hk)
  unfold jetComp
  rw [dif_pos (contOn_iter (f := f + g) (hf.add hg) hk β), dif_pos (contOn_iter hf hk β),
    dif_pos (contOn_iter hg hk β)]
  ext x
  simp only [BoundedContinuousFunction.mkOfCompact_apply, BoundedContinuousFunction.coe_add,
    Pi.add_apply, ContinuousMap.coe_mk]
  change (iteratedFDerivWithin ℝ k (f + g) (simplex m) x.1) _ =
    (iteratedFDerivWithin ℝ k f (simplex m) x.1) _ + (iteratedFDerivWithin ℝ k g (simplex m) x.1) _
  rw [iteratedFDerivWithin_add_apply (hfk x.1 x.2) (hgk x.1 x.2) (uniqueDiffOn_simplex m) x.2]
  rfl

theorem jetComp_smul {m k r : ℕ} (c : ℝ) {f : (Fin m → ℝ) → ℝ} (hf : ContDiffOn ℝ r f (simplex m))
    (hk : k ≤ r) (β : Fin k → Fin m) :
    jetComp (c • f) k β = c • jetComp f k β := by
  have hfk : ContDiffOn ℝ k f (simplex m) := hf.of_le (by exact_mod_cast hk)
  unfold jetComp
  rw [dif_pos (contOn_iter (f := c • f) (hf.const_smul c) hk β), dif_pos (contOn_iter hf hk β)]
  ext x
  simp only [BoundedContinuousFunction.mkOfCompact_apply, BoundedContinuousFunction.coe_smul,
    ContinuousMap.coe_mk]
  change (iteratedFDerivWithin ℝ k (c • f) (simplex m) x.1) _ =
    c • (iteratedFDerivWithin ℝ k f (simplex m) x.1) _
  rw [iteratedFDerivWithin_const_smul_apply (hfk x.1 x.2) (uniqueDiffOn_simplex m) x.2]
  rfl

end FormsLin

section FormsLin2

variable {m r : ℕ}

theorem extD_add (hr : 1 ≤ r) {ω ω' : Ω m} (hω : IsCr r ω) (hω' : IsCr r ω') {x : Fin m → ℝ}
    (hx : x ∈ simplex m) : extD (ω + ω') x = extD ω x + extD ω' x := by
  have hd : ∀ η : Ω m, IsCr r η → ∀ I, DifferentiableWithinAt ℝ (coeff η I) (simplex m) x :=
    fun η h I => ((h I).1.differentiableOn (by exact_mod_cast (show r ≠ 0 by omega))) x hx
  simp only [extD, coeff_add]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← mul_add, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun I _ => ?_
  rw [fderivWithin_add (uniqueDiffOn_simplex m x hx) (hd ω hω I) (hd ω' hω' I)]
  simp [add_smul]

theorem extD_smul (hr : 1 ≤ r) (c : ℝ) {ω : Ω m} (hω : IsCr r ω) {x : Fin m → ℝ}
    (hx : x ∈ simplex m) : extD (c • ω) x = c • extD ω x := by
  have hd : ∀ I, DifferentiableWithinAt ℝ (coeff ω I) (simplex m) x :=
    fun I => ((hω I).1.differentiableOn (by exact_mod_cast (show r ≠ 0 by omega))) x hx
  have e : ∀ I, fderivWithin ℝ (c • coeff ω I) (simplex m) x =
      c • fderivWithin ℝ (coeff ω I) (simplex m) x :=
    fun I => fderivWithin_const_smul (uniqueDiffOn_simplex m x hx) (hd I) c
  simp only [extD, coeff_smul, Finset.smul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← mul_smul_comm, Finset.smul_sum]
  congr 1
  refine Finset.sum_congr rfl fun I _ => ?_
  rw [e I, ContinuousLinearMap.smul_apply, smul_assoc]

theorem isDeg_add {n : ℕ} {ω ω' : Ω m} (h : IsDeg n ω) (h' : IsDeg n ω') : IsDeg n (ω + ω') :=
  fun x hx => Submodule.add_mem _ (h x hx) (h' x hx)

theorem isDeg_smul {n : ℕ} (c : ℝ) {ω : Ω m} (h : IsDeg n ω) : IsDeg n (c • ω) :=
  fun x hx => Submodule.smul_mem _ c (h x hx)

theorem isCr_add (hr : 1 ≤ r) {ω ω' : Ω m} (hω : IsCr r ω) (hω' : IsCr r ω') : IsCr r (ω + ω') := by
  intro I
  refine ⟨by rw [coeff_add]; exact (hω I).1.add (hω' I).1, ((hω I).2.add (hω' I).2).congr ?_⟩
  intro x hx
  show (formBasis m).repr (extD (ω + ω') x) I = coeff (extD ω) I x + coeff (extD ω') I x
  rw [extD_add hr hω hω' hx, map_add]; rfl

theorem isCr_smul (hr : 1 ≤ r) (c : ℝ) {ω : Ω m} (hω : IsCr r ω) : IsCr r (c • ω) := by
  intro I
  refine ⟨by rw [coeff_smul]; exact (hω I).1.const_smul c, ((hω I).2.const_smul c).congr ?_⟩
  intro x hx
  show (formBasis m).repr (extD (c • ω) x) I = c • coeff (extD ω) I x
  rw [extD_smul hr c hω hx, map_smul]; rfl

theorem jet_add (hr : 1 ≤ r) {ω ω' : Ω m} (hω : IsCr r ω) (hω' : IsCr r ω') :
    jet r (ω + ω') = jet r ω + jet r ω' := by
  refine Prod.ext (funext fun I => funext fun k => funext fun β => ?_)
    (funext fun I => funext fun k => funext fun β => ?_)
  · show jetComp (coeff (ω + ω') I) k β = jetComp (coeff ω I) k β + jetComp (coeff ω' I) k β
    rw [coeff_add, jetComp_add (hω I).1 (hω' I).1 (Nat.lt_succ_iff.mp k.2)]
  · show jetComp (coeff (extD (ω + ω')) I) k β =
      jetComp (coeff (extD ω) I) k β + jetComp (coeff (extD ω') I) k β
    rw [jetComp_congr (g := coeff (extD ω) I + coeff (extD ω') I) (fun x hx => by
        show (formBasis m).repr (extD (ω + ω') x) I = coeff (extD ω) I x + coeff (extD ω') I x
        rw [extD_add hr hω hω' hx, map_add]; rfl),
      jetComp_add (hω I).2 (hω' I).2 (Nat.lt_succ_iff.mp k.2)]

theorem jet_smul (hr : 1 ≤ r) (c : ℝ) {ω : Ω m} (hω : IsCr r ω) :
    jet r (c • ω) = c • jet r ω := by
  refine Prod.ext (funext fun I => funext fun k => funext fun β => ?_)
    (funext fun I => funext fun k => funext fun β => ?_)
  · show jetComp (coeff (c • ω) I) k β = c • jetComp (coeff ω I) k β
    rw [coeff_smul, jetComp_smul c (hω I).1 (Nat.lt_succ_iff.mp k.2)]
  · show jetComp (coeff (extD (c • ω)) I) k β = c • jetComp (coeff (extD ω) I) k β
    rw [jetComp_congr (g := c • coeff (extD ω) I) (fun x hx => by
        show (formBasis m).repr (extD (c • ω) x) I = c • coeff (extD ω) I x
        rw [extD_smul hr c hω hx, map_smul]; rfl),
      jetComp_smul c (hω I).2 (Nat.lt_succ_iff.mp k.2)]

theorem isCr_zero : IsCr r (0 : Ω m) := by
  intro I
  have h0 : ∀ J, coeff (0 : Ω m) J = fun _ => 0 := by intro J; funext x; simp [coeff]
  have h1 : extD (0 : Ω m) = 0 := by funext x; simp [extD, h0]
  refine ⟨by rw [h0]; exact contDiffOn_const, by rw [h1, h0]; exact contDiffOn_const⟩

theorem isDeg_zero {n : ℕ} : IsDeg n (0 : Ω m) := fun _ _ => Submodule.zero_mem _

/-- The span in the definition of `CrForms` adds nothing: it is already the image of the jet map. -/
theorem span_jet_eq (hr : 1 ≤ r) (n : ℕ) :
    ((Submodule.span ℝ (jet r '' {ω : Ω m | IsDeg n ω ∧ IsCr r ω}) : Submodule ℝ _) :
      Set (Jet r m × Jet r m)) = jet r '' {ω : Ω m | IsDeg n ω ∧ IsCr r ω} := by
  refine le_antisymm (fun w hw => ?_) Submodule.subset_span
  induction hw using Submodule.span_induction with
  | mem y hy => exact hy
  | zero =>
    refine ⟨0, ⟨isDeg_zero, isCr_zero⟩, ?_⟩
    have := jet_smul (m := m) hr 0 (isCr_zero (m := m) (r := r))
    simpa using this
  | add a b _ _ ha hb =>
    obtain ⟨ω, ⟨h1, h2⟩, rfl⟩ := ha
    obtain ⟨ω', ⟨h1', h2'⟩, rfl⟩ := hb
    exact ⟨ω + ω', ⟨isDeg_add h1 h1', isCr_add hr h2 h2'⟩, jet_add hr h2 h2'⟩
  | smul c a _ ha =>
    obtain ⟨ω, ⟨h1, h2⟩, rfl⟩ := ha
    exact ⟨c • ω, ⟨isDeg_smul c h1, isCr_smul hr c h2⟩, jet_smul hr c h2⟩

theorem crForms_coe (hr : 1 ≤ r) (n : ℕ) :
    (CrForms r m n : Set (Jet r m × Jet r m)) = closure (jet r '' {ω : Ω m | IsDeg n ω ∧ IsCr r ω}) := by
  rw [CrForms, Submodule.topologicalClosure_coe, span_jet_eq hr n]

end FormsLin2

open Filter Topology

section TaylorLimit

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem tendstoUniformlyOn_curryLeft {S : Set E} {j : ℕ}
    {q : ℕ → E → ContinuousMultilinearMap ℝ (fun _ : Fin (j + 1) => E) F}
    {Q : E → ContinuousMultilinearMap ℝ (fun _ : Fin (j + 1) => E) F}
    (h : TendstoUniformlyOn q Q atTop S) :
    TendstoUniformlyOn (fun k x => (q k x).curryLeft) (fun x => (Q x).curryLeft) atTop S := by
  have hu : UniformContinuous
      (fun A : ContinuousMultilinearMap ℝ (fun _ : Fin (j + 1) => E) F => A.curryLeft) :=
    (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (j + 1) => E) F).isometry.uniformContinuous
  exact hu.comp_tendstoUniformlyOn h

theorem taylor_limit {S : Set E} (hconv : Convex ℝ S) (hcl : closure (interior S) = S) {r : ℕ}
    {f : ℕ → E → F} {p : ℕ → E → FormalMultilinearSeries ℝ E F}
    (hp : ∀ k, HasFTaylorSeriesUpToOn r (f k) (p k) S)
    {P : E → FormalMultilinearSeries ℝ E F}
    (hP : ∀ j ≤ r, TendstoUniformlyOn (fun k x => p k x j) (fun x => P x j) atTop S) :
    HasFTaylorSeriesUpToOn r (fun x => (P x 0).curry0) P S := by
  have hcont : ∀ j ≤ r, ContinuousOn (fun x => P x j) S := fun j hj =>
    (hP j hj).continuousOn (Eventually.frequently (Eventually.of_forall fun k =>
      (hp k).cont j (by exact_mod_cast hj)))
  refine ⟨fun x _ => rfl, ?_, fun j hj => hcont j (by exact_mod_cast hj)⟩
  intro j hj x hx
  have hj' : j + 1 ≤ r := by exact_mod_cast hj
  set s := interior S with hs_def
  have hso : IsOpen s := isOpen_interior
  have hsc : Convex ℝ s := hconv.interior
  have hsS : s ⊆ S := interior_subset
  have hder : ∀ y ∈ s, HasFDerivAt (fun x => P x j) (P y (j + 1)).curryLeft y := by
    intro y hy
    refine hasFDerivAt_of_tendstoUniformlyOn (l := atTop) hso
      (f := fun k x => p k x j) (f' := fun k x => (p k x (j + 1)).curryLeft)
      ((tendstoUniformlyOn_curryLeft ((hP (j + 1) hj').mono hsS))) ?_ ?_ hy
    · intro k z hz
      exact ((hp k).fderivWithin j (by exact_mod_cast hj) z (hsS hz)).hasFDerivAt
        (mem_interior_iff_mem_nhds.mp hz)
    · intro z hz
      exact (hP j (by omega)).tendsto_at (hsS hz)
  have hG'cont : ContinuousOn (fun x => (P x (j + 1)).curryLeft) S := by
    have := hcont (j + 1) hj'
    exact (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (j + 1) => E) F).continuous.comp_continuousOn
      this
  have key := hasFDerivWithinAt_closure_of_tendsto_fderiv (f := fun x => P x j)
    (f' := (P x (j + 1)).curryLeft) (x := x)
    (fun y hy => (hder y hy).differentiableAt.differentiableWithinAt) hsc hso
    (fun y hy => by
      rw [hcl] at hy
      exact ((hcont j (by omega)) y hy).mono hsS)
    (by
      have h1 : Tendsto (fun y => (P y (j + 1)).curryLeft) (𝓝[s] x) (𝓝 (P x (j + 1)).curryLeft) :=
        ((hG'cont x hx).mono hsS).tendsto
      refine h1.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with y hy
      exact (hder y hy).fderiv.symm)
  rwa [hcl] at key

end TaylorLimit

section JetLimit

open IntLInfty.Kan BoundedContinuousFunction

theorem isClosed_simplex (m : ℕ) : IsClosed (simplex m) := by
  have h1 : IsClosed {t : Fin m → ℝ | ∀ i, 0 ≤ t i} := by
    simpa only [Set.ofPred_forall] using
      isClosed_iInter fun i => isClosed_le continuous_const (continuous_apply i)
  have h2 : IsClosed {t : Fin m → ℝ | ∑ i, t i ≤ 1} :=
    isClosed_le (continuous_finsetSum _ fun i _ => continuous_apply i) continuous_const
  exact h1.inter h2

theorem closure_interior_simplex (m : ℕ) : closure (interior (simplex m)) = simplex m := by
  rw [(convex_simplex m).closure_interior_eq_closure_of_nonempty_interior
    (interior_simplex_nonempty m)]
  exact (isClosed_simplex m).closure_eq

theorem jetComp_apply {m r : ℕ} {f : (Fin m → ℝ) → ℝ} (hf : ContDiffOn ℝ r f (simplex m)) {k : ℕ}
    (hk : k ≤ r) (β : Fin k → Fin m) {x : Fin m → ℝ} (hx : x ∈ simplex m) :
    jetComp f k β ⟨x, hx⟩ = iteratedFDerivWithin ℝ k f (simplex m) x (fun l => Pi.single (β l) 1) := by
  unfold jetComp
  rw [dif_pos (contOn_iter hf hk β)]
  rfl

theorem norm_cmm_le_sum {m j : ℕ} (M : ContinuousMultilinearMap ℝ (fun _ : Fin j => Fin m → ℝ) ℝ) :
    ‖M‖ ≤ ∑ β : Fin j → Fin m, |M (fun l => Pi.single (β l) 1)| := by
  refine M.opNorm_le_bound (Finset.sum_nonneg fun _ _ => abs_nonneg _) fun v => ?_
  have hv : v = fun l => ∑ i : Fin m, v l i • (Pi.single i (1 : ℝ) : Fin m → ℝ) := by
    funext l; ext t; simp [Finset.sum_apply, Pi.single_apply]
  have hexp : M v = ∑ β : Fin j → Fin m, (∏ l, v l (β l)) • M (fun l => Pi.single (β l) 1) := by
    conv_lhs => rw [hv]
    rw [M.map_sum]
    refine Finset.sum_congr rfl fun β _ => ?_
    exact M.map_smul_univ _ _
  rw [hexp, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun β _ => ?_)
  rw [norm_smul, norm_prod, Real.norm_eq_abs, mul_comm]
  exact mul_le_mul_of_nonneg_left (Finset.prod_le_prod (fun _ _ => norm_nonneg _)
    fun l _ => norm_le_pi_norm (v l) (β l)) (abs_nonneg _)

/-- Sub-lemma A: a limit (in the jet norm) of jets of `Cʳ` functions on the simplex is the jet of a
`Cʳ` function. -/
theorem jet_limit {m r : ℕ} {f : ℕ → (Fin m → ℝ) → ℝ} (hf : ∀ k, ContDiffOn ℝ r (f k) (simplex m))
    {g : (j : Fin (r + 1)) → (Fin (j : ℕ) → Fin m) → (simplex m →ᵇ ℝ)}
    (hg : ∀ (j : Fin (r + 1)) β, Tendsto (fun k => jetComp (f k) j β) atTop (𝓝 (g j β))) :
    ∃ F : (Fin m → ℝ) → ℝ, ContDiffOn ℝ r F (simplex m) ∧
      ∀ (j : Fin (r + 1)) β, jetComp F j β = g j β := by
  have hU : UniqueDiffOn ℝ (simplex m) := uniqueDiffOn_simplex m
  have hCau : ∀ j : Fin (r + 1),
      UniformCauchySeqOn (fun k x => iteratedFDerivWithin ℝ j (f k) (simplex m) x) atTop (simplex m) := by
    intro j
    let J : ℕ → (Fin (j : ℕ) → Fin m) → (simplex m →ᵇ ℝ) := fun k β => jetComp (f k) j β
    have hJ : Tendsto J atTop (𝓝 fun β => g j β) := tendsto_pi_nhds.mpr fun β => hg j β
    have hJc := hJ.cauchySeq
    rw [Metric.cauchySeq_iff] at hJc
    rw [Metric.uniformCauchySeqOn_iff]
    intro ε hε
    set c : ℝ := (Fintype.card (Fin (j : ℕ) → Fin m) : ℝ) + 1 with hc_def
    have hc : 0 < c := by positivity
    obtain ⟨N, hN⟩ := hJc (ε / c) (div_pos hε hc)
    refine ⟨N, fun a ha b hb x hx => ?_⟩
    have hab := hN a ha b hb
    rw [dist_eq_norm] at hab ⊢
    refine lt_of_le_of_lt (norm_cmm_le_sum _) ?_
    have hterm : ∀ β : Fin (j : ℕ) → Fin m,
        |(iteratedFDerivWithin ℝ j (f a) (simplex m) x - iteratedFDerivWithin ℝ j (f b) (simplex m) x)
          (fun l => Pi.single (β l) 1)| ≤ ε / c := by
      intro β
      rw [_root_.sub_apply, ← jetComp_apply (hf a) (Fin.is_le j) β hx,
        ← jetComp_apply (hf b) (Fin.is_le j) β hx]
      calc |jetComp (f a) j β ⟨x, hx⟩ - jetComp (f b) j β ⟨x, hx⟩|
          = ‖(J a β - J b β) ⟨x, hx⟩‖ := by rw [Real.norm_eq_abs]; rfl
        _ ≤ ‖J a β - J b β‖ := BoundedContinuousFunction.norm_coe_le_norm _ _
        _ ≤ ‖J a - J b‖ := norm_le_pi_norm (J a - J b) β
        _ ≤ ε / c := hab.le
    calc ∑ β : Fin (j : ℕ) → Fin m, |(iteratedFDerivWithin ℝ j (f a) (simplex m) x -
          iteratedFDerivWithin ℝ j (f b) (simplex m) x) (fun l => Pi.single (β l) 1)|
        ≤ ∑ _β : Fin (j : ℕ) → Fin m, ε / c := Finset.sum_le_sum fun β _ => hterm β
      _ = (Fintype.card (Fin (j : ℕ) → Fin m) : ℝ) * (ε / c) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ < c * (ε / c) := by
          apply mul_lt_mul_of_pos_right _ (div_pos hε hc)
          rw [hc_def]; linarith
      _ = ε := by field_simp
  let P : (Fin m → ℝ) → FormalMultilinearSeries ℝ (Fin m → ℝ) ℝ := fun x j =>
    limUnder atTop (fun k => iteratedFDerivWithin ℝ j (f k) (simplex m) x)
  have hPt : ∀ j : Fin (r + 1), ∀ x ∈ (simplex m),
      Tendsto (fun k => iteratedFDerivWithin ℝ j (f k) (simplex m) x) atTop (𝓝 (P x j)) :=
    fun j x hx => ((hCau j).cauchySeq hx).tendsto_limUnder
  have hP : ∀ j ≤ r, TendstoUniformlyOn (fun k x => ftaylorSeriesWithin ℝ (f k) (simplex m) x j)
      (fun x => P x j) atTop (simplex m) := by
    intro j hj
    exact (hCau ⟨j, Nat.lt_succ_of_le hj⟩).tendstoUniformlyOn_of_tendsto
      (hPt ⟨j, Nat.lt_succ_of_le hj⟩)
  have H := taylor_limit (convex_simplex m) (closure_interior_simplex m)
    (fun k => (hf k).ftaylorSeriesWithin hU) hP
  have hFc : ContDiffOn ℝ r (fun x => (P x 0).curry0) (simplex m) := H.contDiffOn
  refine ⟨fun x => (P x 0).curry0, hFc, fun j β => ?_⟩
  ext ⟨x, hx⟩
  rw [jetComp_apply hFc (Fin.is_le j) β hx,
    ← H.eq_iteratedFDerivWithin_of_uniqueDiffOn (by exact_mod_cast Fin.is_le j) hU hx]
  have h1 : Tendsto (fun k => jetComp (f k) j β ⟨x, hx⟩) atTop (𝓝 (g j β ⟨x, hx⟩)) :=
    ((continuous_eval_const (⟨x, hx⟩ : ↥(simplex m))).tendsto _).comp (hg j β)
  have h2 : Tendsto (fun k => jetComp (f k) j β ⟨x, hx⟩) atTop
      (𝓝 (P x j (fun l => Pi.single (β l) 1))) := by
    have := ((continuous_eval_const (fun l => Pi.single (β l) (1 : ℝ))).tendsto
      _).comp (hPt j x hx)
    refine this.congr fun k => ?_
    exact (jetComp_apply (hf k) (Fin.is_le j) β hx).symm
  exact tendsto_nhds_unique h2 h1

end JetLimit

section JetClosed

open IntLInfty.Kan BoundedContinuousFunction

theorem jetComp_zero {m r : ℕ} {f : (Fin m → ℝ) → ℝ} (hf : ContDiffOn ℝ r f (simplex m)) {k : ℕ}
    (hk : k = 0) (β : Fin k → Fin m) {x : Fin m → ℝ} (hx : x ∈ simplex m) :
    jetComp f k β ⟨x, hx⟩ = f x := by
  subst hk
  rw [jetComp_apply hf (Nat.zero_le _) β hx]
  rfl

theorem jetComp_one {m r : ℕ} {f : (Fin m → ℝ) → ℝ} (hf : ContDiffOn ℝ r f (simplex m)) (hr : 1 ≤ r)
    (β : Fin 1 → Fin m) {x : Fin m → ℝ} (hx : x ∈ simplex m) :
    jetComp f 1 β ⟨x, hx⟩ = fderivWithin ℝ f (simplex m) x (Pi.single (β 0) 1) := by
  rw [jetComp_apply hf hr β hx, iteratedFDerivWithin_one_apply (uniqueDiffOn_simplex m x hx)]

theorem continuous_jet_eval {r m : ℕ} (I : Finset (Fin m)) (j : Fin (r + 1))
    (β : Fin (j : ℕ) → Fin m) : Continuous (fun w : Jet r m => w I j β) := by
  have : Continuous (fun w : ((I : Finset (Fin m)) → (k : Fin (r + 1)) → (Fin (k : ℕ) → Fin m) →
      (simplex m →ᵇ ℝ)) => w I j β) :=
    (continuous_apply β).comp ((continuous_apply j).comp (continuous_apply I))
  exact this

theorem coeff_extD {m : ℕ} (ω : Ω m) (I : Finset (Fin m)) (x : Fin m → ℝ) :
    coeff (extD ω) I x = ∑ k : Fin m, ∑ J : Finset (Fin m),
      fderivWithin ℝ (coeff ω J) (simplex m) x (Pi.single k 1) *
        (formBasis m).repr (dx m k * formBasis m J) I := by
  simp only [coeff, extD, Finset.mul_sum, mul_smul_comm, map_sum, map_smul, Finsupp.coe_finsetSum,
    Finset.sum_apply, Finsupp.smul_apply, smul_eq_mul]

/-- A limit of jets of degree-`n` `Cʳ` forms is the jet of such a form `Ω0`; moreover the
coefficients of `d ω_k` converge pointwise on the simplex to those of `d Ω0`. -/
theorem jet_seq_limit {r m : ℕ} (hr : 1 ≤ r) (n : ℕ) {ω : ℕ → Ω m}
    (hω : ∀ k, IsDeg n (ω k) ∧ IsCr r (ω k)) {w : ℕ → Jet r m × Jet r m}
    (hωw : ∀ k, jet r (ω k) = w k) {p : Jet r m × Jet r m} (hlim : Tendsto w atTop (𝓝 p)) :
    ∃ Ω0 : Ω m, (IsDeg n Ω0 ∧ IsCr r Ω0) ∧ jet r Ω0 = p ∧
      ∀ I, ∀ x ∈ simplex m, Tendsto (fun k => coeff (extD (ω k)) I x) atTop
        (𝓝 (coeff (extD Ω0) I x)) := by
  have h1 : ∀ I (j : Fin (r + 1)) β,
      Tendsto (fun k => jetComp (coeff (ω k) I) j β) atTop (𝓝 (p.1 I j β)) := by
    intro I j β
    have := ((((continuous_jet_eval I j β).comp continuous_fst)).tendsto p).comp hlim
    refine this.congr fun k => ?_
    simp only [Function.comp_apply, ← hωw k, jet]
  have h2 : ∀ I (j : Fin (r + 1)) β,
      Tendsto (fun k => jetComp (coeff (extD (ω k)) I) j β) atTop (𝓝 (p.2 I j β)) := by
    intro I j β
    have := ((((continuous_jet_eval I j β).comp continuous_snd)).tendsto p).comp hlim
    refine this.congr fun k => ?_
    simp only [Function.comp_apply, ← hωw k, jet]
  choose F hF hFj using fun I => jet_limit (fun k => ((hω k).2 I).1) (h1 I)
  choose G hG hGj using fun I => jet_limit (fun k => ((hω k).2 I).2) (h2 I)
  let Ω0 : Ω m := fun x => (formBasis m).equivFun.symm (fun I => F I x)
  have hcoeff : ∀ I, coeff Ω0 I = F I := by
    intro I; funext x
    show (formBasis m).repr ((formBasis m).equivFun.symm (fun I => F I x)) I = F I x
    rw [← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply]
  let j0 : Fin (r + 1) := 0
  have β0 : Fin (j0 : ℕ) → Fin m := fun l => absurd l.isLt (by simp [j0])
  have hj0 : (j0 : ℕ) = 0 := rfl
  have hpt0 : ∀ I x (hx : x ∈ simplex m),
      Tendsto (fun k => coeff (ω k) I x) atTop (𝓝 (F I x)) := by
    intro I x hx
    have := ((continuous_eval_const (⟨x, hx⟩ : ↥(simplex m))).tendsto _).comp (h1 I j0 β0)
    rw [← hFj I j0 β0, jetComp_zero (hF I) hj0 β0 hx] at this
    refine this.congr fun k => ?_
    exact jetComp_zero ((hω k).2 I).1 hj0 β0 hx
  have hptG : ∀ I x (hx : x ∈ simplex m),
      Tendsto (fun k => coeff (extD (ω k)) I x) atTop (𝓝 (G I x)) := by
    intro I x hx
    have := ((continuous_eval_const (⟨x, hx⟩ : ↥(simplex m))).tendsto _).comp (h2 I j0 β0)
    rw [← hGj I j0 β0, jetComp_zero (hG I) hj0 β0 hx] at this
    refine this.congr fun k => ?_
    exact jetComp_zero ((hω k).2 I).2 hj0 β0 hx
  let j1 : Fin (r + 1) := ⟨1, by omega⟩
  have hpt1 : ∀ J (q : Fin m) x (hx : x ∈ simplex m),
      Tendsto (fun k => fderivWithin ℝ (coeff (ω k) J) (simplex m) x (Pi.single q 1)) atTop
        (𝓝 (fderivWithin ℝ (coeff Ω0 J) (simplex m) x (Pi.single q 1))) := by
    intro J q x hx
    have := ((continuous_eval_const (⟨x, hx⟩ : ↥(simplex m))).tendsto _).comp
      (h1 J j1 (fun _ => q))
    rw [← hFj J j1 (fun _ => q)] at this
    have e1 : jetComp (F J) (j1 : ℕ) (fun _ => q) ⟨x, hx⟩ =
        fderivWithin ℝ (coeff Ω0 J) (simplex m) x (Pi.single q 1) := by
      rw [hcoeff J]; exact jetComp_one (hF J) hr (fun _ => q) hx
    rw [e1] at this
    refine this.congr fun k => ?_
    exact jetComp_one ((hω k).2 J).1 hr (fun _ => q) hx
  have hext : ∀ I, ∀ x ∈ simplex m, coeff (extD Ω0) I x = G I x := by
    intro I x hx
    have hA : Tendsto (fun k => coeff (extD (ω k)) I x) atTop (𝓝 (coeff (extD Ω0) I x)) := by
      simp only [coeff_extD]
      exact tendsto_finsetSum _ fun q _ => tendsto_finsetSum _ fun J _ =>
        (hpt1 J q x hx).mul_const _
    exact tendsto_nhds_unique hA (hptG I x hx)
  have hDeg : IsDeg n Ω0 := by
    intro x hx
    let W := (⋀[ℝ]^n (Module.Dual ℝ (Fin m → ℝ))).map
      (formBasis m).equivFun.toLinearMap
    have hWc : IsClosed (W : Set (Finset (Fin m) → ℝ)) := W.closed_of_finiteDimensional
    have hT : Tendsto (fun k => (formBasis m).equivFun (ω k x)) atTop (𝓝 fun I => F I x) := by
      refine tendsto_pi_nhds.mpr fun I => (hpt0 I x hx).congr fun k => ?_
      rw [Module.Basis.equivFun_apply]; rfl
    have hmem : (fun I => F I x) ∈ W := hWc.mem_of_tendsto hT
      (Eventually.of_forall fun k => Submodule.mem_map_of_mem ((hω k).1 x hx))
    obtain ⟨v, hv, hve⟩ := Submodule.mem_map.mp hmem
    have : Ω0 x = v := by
      show (formBasis m).equivFun.symm (fun I => F I x) = v
      rw [← hve]; exact LinearEquiv.symm_apply_apply _ v
    rw [this]; exact hv
  have hCr : IsCr r Ω0 := fun I =>
    ⟨(hcoeff I).symm ▸ hF I, (hG I).congr fun x hx => hext I x hx⟩
  refine ⟨Ω0, ⟨hDeg, hCr⟩, ?_, fun I x hx => by rw [hext I x hx]; exact hptG I x hx⟩
  refine Prod.ext ?_ ?_
  · show (fun I (k : Fin (r + 1)) β => jetComp (coeff Ω0 I) k β) = p.1
    funext I j β
    rw [hcoeff I, hFj I j β]
  · show (fun I (k : Fin (r + 1)) β => jetComp (coeff (extD Ω0) I) k β) = p.2
    funext I j β
    rw [jetComp_congr (hext I) β, hGj I j β]

theorem jetImage_closed {r m : ℕ} (hr : 1 ≤ r) (n : ℕ) :
    IsClosed (jet r '' {ω : Ω m | IsDeg n ω ∧ IsCr r ω}) := by
  refine IsSeqClosed.isClosed fun w p hw hlim => ?_
  choose ω hω hωw using hw
  obtain ⟨Ω0, h0, hj, -⟩ := jet_seq_limit hr n hω hωw hlim
  exact ⟨Ω0, h0, hj⟩

end JetClosed

theorem crForms_eq_image {r m : ℕ} (hr : 1 ≤ r) (n : ℕ) :
    (CrForms r m n : Set (Jet r m × Jet r m)) = jet r '' {ω : Ω m | IsDeg n ω ∧ IsCr r ω} := by
  rw [crForms_coe hr n, (jetImage_closed hr n).closure_eq]

section ClosedSpan

variable {m r : ℕ}

end ClosedSpan

section Rep

/-! Representative independence: the jet of a form only depends on its values on the simplex, and
it determines those values; hence `faceCr`, `faceCl`, `dCr` are computed by any representative. -/

variable {m r : ℕ}

/-- Two forms agree on the simplex. -/
def FormEqOn (ω ω' : Ω m) : Prop := ∀ x ∈ simplex m, ω x = ω' x

theorem coeff_eqOn {ω ω' : Ω m} (h : FormEqOn ω ω') (I : Finset (Fin m)) :
    Set.EqOn (coeff ω I) (coeff ω' I) (simplex m) := fun x hx => by
  simp only [coeff, h x hx]

theorem extD_congr {ω ω' : Ω m} (h : FormEqOn ω ω') : FormEqOn (extD ω) (extD ω') := by
  intro x hx
  simp only [extD]
  refine Finset.sum_congr rfl fun k _ => ?_
  congr 1
  refine Finset.sum_congr rfl fun I _ => ?_
  rw [fderivWithin_congr (coeff_eqOn h I) (coeff_eqOn h I hx)]

theorem jet_congr {ω ω' : Ω m} (h : FormEqOn ω ω') : jet r ω = jet r ω' := by
  have h1 : ∀ I, ∀ k (β : Fin k → Fin m),
      jetComp (coeff ω I) k β = jetComp (coeff ω' I) k β :=
    fun I _ β => jetComp_congr (coeff_eqOn h I) β
  have h2 : ∀ I, ∀ k (β : Fin k → Fin m),
      jetComp (coeff (extD ω) I) k β = jetComp (coeff (extD ω') I) k β :=
    fun I _ β => jetComp_congr (coeff_eqOn (extD_congr h) I) β
  simp only [jet, h1, h2]

theorem formEqOn_of_jet {ω ω' : Ω m} (hω : IsCr r ω) (hω' : IsCr r ω')
    (h : jet r ω = jet r ω') : FormEqOn ω ω' := by
  intro x hx
  refine (formBasis m).ext_elem fun I => ?_
  let j0 : Fin (r + 1) := 0
  have hj0 : (j0 : ℕ) = 0 := rfl
  have β0 : Fin (j0 : ℕ) → Fin m := fun l => absurd l.isLt (by simp [j0])
  have e : (jet r ω).1 I j0 β0 = (jet r ω').1 I j0 β0 := by rw [h]
  simp only [jet] at e
  have e2 := congrArg (fun g : BoundedContinuousFunction (simplex m) ℝ => g ⟨x, hx⟩) e
  rw [jetComp_zero (hω I).1 hj0 β0 hx, jetComp_zero (hω' I).1 hj0 β0 hx] at e2
  exact e2

theorem vertex_mem (m : ℕ) (j : Fin (m + 1)) : vertex m j ∈ simplex m := by
  induction j using Fin.cases with
  | zero => exact ⟨fun _ => le_refl _, by simp [vertex]⟩
  | succ k =>
    simp only [vertex, Fin.cases_succ]
    refine ⟨fun a => ?_, ?_⟩
    · by_cases hak : a = k
      · subst hak; simp
      · simp [hak]
    · simp

theorem coface_eq (i : Fin (m + 2)) (x : Fin m → ℝ) :
    coface m i x = vertex (m + 1) (i.succAbove 0) + ∑ k, x k •
      (vertex (m + 1) (i.succAbove k.succ) - vertex (m + 1) (i.succAbove 0)) := by
  funext a
  simp [coface, cofaceLin, Matrix.mulVec, dotProduct, mul_comm]

theorem coface_mem (i : Fin (m + 2)) {x : Fin m → ℝ} (hx : x ∈ simplex m) :
    coface m i x ∈ simplex (m + 1) := by
  let w : Fin (m + 1) → ℝ := Fin.cons (1 - ∑ k, x k) x
  have h0 : ∀ j ∈ (Finset.univ : Finset (Fin (m + 1))), 0 ≤ w j := by
    intro j _
    induction j using Fin.cases with
    | zero => simp only [w, Fin.cons_zero]; linarith [hx.2]
    | succ k => simp only [w, Fin.cons_succ]; exact hx.1 k
  have h1 : ∑ j, w j = 1 := by
    rw [Fin.sum_univ_succ]; simp only [w, Fin.cons_zero, Fin.cons_succ]; ring
  have hm := (convex_simplex (m + 1)).sum_mem h0 h1
    (z := fun j => vertex (m + 1) (i.succAbove j)) (fun j _ => vertex_mem _ _)
  convert hm using 1
  rw [coface_eq, Fin.sum_univ_succ]
  simp only [w, Fin.cons_zero, Fin.cons_succ, smul_sub, Finset.sum_sub_distrib, sub_smul,
    one_smul, ← Finset.sum_smul]
  abel

theorem pull_congr (i : Fin (m + 2)) {ω ω' : Ω (m + 1)} (h : FormEqOn ω ω') :
    FormEqOn (pull m i ω) (pull m i ω') := fun x hx => by
  simp only [pull]; rw [h _ (coface_mem i hx)]

theorem viaRep_spec {m' n : ℕ} {V : Submodule ℝ (Jet r m' × Jet r m')} {F : Ω m → Ω m'}
    (hF : ∀ ω ω' : Ω m, FormEqOn ω ω' → FormEqOn (F ω) (F ω')) {ω : Ω m} (hD : IsDeg n ω)
    (hC : IsCr r ω) (hV : jet r (F ω) ∈ V) :
    (viaRep n V F (jet r ω) : Jet r m' × Jet r m') = jet r (F ω) := by
  have hex : ∃ ω' : Ω m, IsDeg n ω' ∧ IsCr r ω' ∧ jet r ω' = jet r ω ∧ jet r (F ω') ∈ V :=
    ⟨ω, hD, hC, rfl, hV⟩
  simp only [viaRep, dif_pos hex]
  exact jet_congr (hF _ _ (formEqOn_of_jet hex.choose_spec.2.1 hC hex.choose_spec.2.2.1))

theorem faceCr_spec {n : ℕ} (i : Fin (m + 2)) {ω : Ω (m + 1)} (hD : IsDeg n ω) (hC : IsCr r ω)
    (hw : jet r ω ∈ CrForms r (m + 1) n) (hV : jet r (pull m i ω) ∈ CrForms r m n) :
    (faceCr r m n i ⟨jet r ω, hw⟩ : Jet r m × Jet r m) = jet r (pull m i ω) :=
  viaRep_spec (fun _ _ h => pull_congr i h) hD hC hV

end Rep

section Pull

/-! Pullback along cofaces preserves degree and the `Cʳ` condition, and commutes with `d`. -/

variable {m r : ℕ}

theorem map_mem_exteriorPower {M N : Type} [AddCommGroup M] [Module ℝ M] [AddCommGroup N]
    [Module ℝ N] (f : M →ₗ[ℝ] N) {n : ℕ} {a : ExteriorAlgebra ℝ M} (ha : a ∈ ⋀[ℝ]^n M) :
    ExteriorAlgebra.map f a ∈ ⋀[ℝ]^n N := by
  have h1 : (⋀[ℝ]^n M).map (ExteriorAlgebra.map f).toLinearMap ≤ ⋀[ℝ]^n N := by
    show Submodule.map _ (LinearMap.range (ExteriorAlgebra.ι ℝ) ^ n) ≤
      LinearMap.range (ExteriorAlgebra.ι ℝ) ^ n
    rw [Submodule.map_pow]
    refine pow_le_pow_left' ?_ n
    rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
    exact ⟨f x, (ExteriorAlgebra.map_apply_ι f x).symm⟩
  exact h1 (Submodule.mem_map_of_mem ha)

theorem pull_isDeg {n : ℕ} (i : Fin (m + 2)) {ω : Ω (m + 1)} (h : IsDeg n ω) :
    IsDeg n (pull m i ω) := fun x hx =>
  map_mem_exteriorPower _ (h _ (coface_mem i hx))

theorem coeff_pull (i : Fin (m + 2)) (ω : Ω (m + 1)) (J : Finset (Fin m)) (x : Fin m → ℝ) :
    coeff (pull m i ω) J x = ∑ I, coeff ω I (coface m i x) *
      (formBasis m).repr (ExteriorAlgebra.map (cofaceLin m i).dualMap (formBasis (m + 1) I)) J := by
  simp only [coeff, pull]
  conv_lhs => rw [← (formBasis (m + 1)).sum_repr (ω (coface m i x))]
  simp only [map_sum, map_smul, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.smul_apply,
    smul_eq_mul]

theorem coface_eq_clm (i : Fin (m + 2)) : coface m i =
    fun x => vertex (m + 1) (i.succAbove 0) + LinearMap.toContinuousLinearMap (cofaceLin m i) x :=
  rfl

theorem hasFDerivAt_coface (i : Fin (m + 2)) (x : Fin m → ℝ) :
    HasFDerivAt (coface m i) (LinearMap.toContinuousLinearMap (cofaceLin m i)) x := by
  rw [coface_eq_clm]
  exact (LinearMap.toContinuousLinearMap (cofaceLin m i)).hasFDerivAt.const_add _

theorem contDiff_coface {n : WithTop ℕ∞} (i : Fin (m + 2)) : ContDiff ℝ n (coface m i) := by
  rw [coface_eq_clm]
  exact contDiff_const.add (ContinuousLinearMap.contDiff _)

theorem contDiffOn_coeff_pull (i : Fin (m + 2)) {ω : Ω (m + 1)}
    (h : ∀ I, ContDiffOn ℝ r (coeff ω I) (simplex (m + 1))) (J : Finset (Fin m)) :
    ContDiffOn ℝ r (coeff (pull m i ω) J) (simplex m) := by
  have e : coeff (pull m i ω) J = fun x => ∑ I, coeff ω I (coface m i x) *
      (formBasis m).repr (ExteriorAlgebra.map (cofaceLin m i).dualMap (formBasis (m + 1) I)) J :=
    funext (coeff_pull i ω J)
  rw [e]
  exact ContDiffOn.sum fun I _ =>
    ((h I).comp (contDiff_coface i).contDiffOn (fun x hx => coface_mem i hx)).mul contDiffOn_const

theorem dualMap_proj {m' : ℕ} (L : (Fin m → ℝ) →ₗ[ℝ] (Fin m' → ℝ)) (a : Fin m') :
    L.dualMap (LinearMap.proj a) =
      ∑ k, (L (Pi.single k 1) a) • (LinearMap.proj k : (Fin m → ℝ) →ₗ[ℝ] ℝ) := by
  ext j
  simp [LinearMap.dualMap_apply, Pi.single_apply]

theorem linear_expand {m' : ℕ} {A : Type} [AddCommGroup A] [Module ℝ A]
    (T : (Fin m' → ℝ) →ₗ[ℝ] A) (v : Fin m' → ℝ) : T v = ∑ a, v a • T (Pi.single a 1) := by
  conv_lhs => rw [← (Pi.basisFun ℝ (Fin m')).sum_repr v]
  simp only [map_sum, map_smul, Pi.basisFun_apply, Pi.basisFun_repr]

theorem wedge_natural {m' : ℕ} (L : (Fin m → ℝ) →ₗ[ℝ] (Fin m' → ℝ))
    (T : (Fin m' → ℝ) →ₗ[ℝ] ExteriorAlgebra ℝ (Module.Dual ℝ (Fin m' → ℝ))) :
    ExteriorAlgebra.map L.dualMap (∑ a, dx m' a * T (Pi.single a 1)) =
      ∑ k, dx m k * ExteriorAlgebra.map L.dualMap (T (L (Pi.single k 1))) := by
  simp only [map_sum, map_mul, dx, ExteriorAlgebra.map_apply_ι, dualMap_proj, map_smul,
    Finset.sum_mul, smul_mul_assoc]
  conv_rhs => enter [2, k]; rw [linear_expand T (L (Pi.single k 1))]
  simp only [map_sum, map_smul, Finset.mul_sum, mul_smul_comm]
  exact Finset.sum_comm

/-- The coefficients of the pulled-back basis forms. -/
noncomputable def pc (i : Fin (m + 2)) (I : Finset (Fin (m + 1))) (J : Finset (Fin m)) : ℝ :=
  (formBasis m).repr (ExteriorAlgebra.map (cofaceLin m i).dualMap (formBasis (m + 1) I)) J

theorem extD_pull (hr : 1 ≤ r) (i : Fin (m + 2)) {ω : Ω (m + 1)}
    (hC : ∀ I, ContDiffOn ℝ r (coeff ω I) (simplex (m + 1))) {x : Fin m → ℝ}
    (hx : x ∈ simplex m) : extD (pull m i ω) x = pull m i (extD ω) x := by
  have hy : coface m i x ∈ simplex (m + 1) := coface_mem i hx
  have hd : ∀ I, HasFDerivWithinAt (coeff ω I)
      (fderivWithin ℝ (coeff ω I) (simplex (m + 1)) (coface m i x)) (simplex (m + 1))
      (coface m i x) := fun I =>
    (((hC I).differentiableOn (by exact_mod_cast (show r ≠ 0 by omega))) _ hy).hasFDerivWithinAt
  have hpd : ∀ J (k : Fin m), fderivWithin ℝ (coeff (pull m i ω) J) (simplex m) x (Pi.single k 1) =
      ∑ I, fderivWithin ℝ (coeff ω I) (simplex (m + 1)) (coface m i x)
        (cofaceLin m i (Pi.single k 1)) * pc i I J := by
    intro J k
    have e : coeff (pull m i ω) J = fun x => ∑ I, coeff ω I (coface m i x) * pc i I J :=
      funext (coeff_pull i ω J)
    have hH : HasFDerivWithinAt (fun x => ∑ I, coeff ω I (coface m i x) * pc i I J)
        (∑ I, (pc i I J) • ((fderivWithin ℝ (coeff ω I) (simplex (m + 1)) (coface m i x)).comp
          (LinearMap.toContinuousLinearMap (cofaceLin m i)))) (simplex m) x := by
      refine HasFDerivWithinAt.fun_sum (u := Finset.univ) fun I _ => ?_
      exact ((hd I).comp x (hasFDerivAt_coface i x).hasFDerivWithinAt
        (fun z hz => coface_mem i hz)).mul_const (pc i I J)
    rw [e, hH.fderivWithin (uniqueDiffOn_simplex m x hx)]
    simp [mul_comm]
  let T : (Fin (m + 1) → ℝ) →ₗ[ℝ] ExteriorAlgebra ℝ (Module.Dual ℝ (Fin (m + 1) → ℝ)) :=
    ∑ I, ((fderivWithin ℝ (coeff ω I) (simplex (m + 1)) (coface m i x) :
      (Fin (m + 1) → ℝ) →L[ℝ] ℝ) : (Fin (m + 1) → ℝ) →ₗ[ℝ] ℝ).smulRight (formBasis (m + 1) I)
  have hT : ∀ v, T v = ∑ I, fderivWithin ℝ (coeff ω I) (simplex (m + 1)) (coface m i x) v •
      formBasis (m + 1) I := by
    intro v; simp [T]
  have hR : pull m i (extD ω) x = ExteriorAlgebra.map (cofaceLin m i).dualMap
      (∑ a, dx (m + 1) a * T (Pi.single a 1)) := by
    simp only [hT]; rfl
  rw [hR, wedge_natural]
  simp only [extD]
  refine Finset.sum_congr rfl fun k _ => ?_
  congr 1
  rw [hT]
  simp only [hpd, map_sum, map_smul, Finset.sum_smul, mul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun I _ => ?_
  rw [← Finset.smul_sum]
  congr 1
  exact (formBasis m).sum_repr _

theorem pull_isCr (hr : 1 ≤ r) (i : Fin (m + 2)) {ω : Ω (m + 1)} (hC : IsCr r ω) :
    IsCr r (pull m i ω) := fun J =>
  ⟨contDiffOn_coeff_pull i (fun I => (hC I).1) J,
    (contDiffOn_coeff_pull i (fun I => (hC I).2) J).congr fun x hx => by
      show (formBasis m).repr (extD (pull m i ω) x) J = (formBasis m).repr (pull m i (extD ω) x) J
      rw [extD_pull hr i (fun I => (hC I).1) hx]⟩

theorem faceCr_eq {n : ℕ} (hr : 1 ≤ r) (i : Fin (m + 2)) {ω : Ω (m + 1)} (hD : IsDeg n ω)
    (hC : IsCr r ω) (hw : jet r ω ∈ CrForms r (m + 1) n) :
    (faceCr r m n i ⟨jet r ω, hw⟩ : Jet r m × Jet r m) = jet r (pull m i ω) := by
  refine faceCr_spec i hD hC hw ?_
  show jet r (pull m i ω) ∈ (CrForms r m n : Set (Jet r m × Jet r m))
  rw [crForms_eq_image hr n]
  exact ⟨_, ⟨pull_isDeg i hD, pull_isCr hr i hC⟩, rfl⟩

end Pull

section PullAff

/-! Pullback along an arbitrary affine map `x ↦ b + L x` sending `Δᵐ` into `Δᵐ'` (the retractions
used by the horn-extension operator of Lemma 5.9 are of this kind). -/

variable {m m' r : ℕ}

/-- Pullback of forms along the affine map `x ↦ b + L x`. -/
noncomputable def pullA (b : Fin m' → ℝ) (L : (Fin m → ℝ) →ₗ[ℝ] (Fin m' → ℝ)) (ω : Ω m') : Ω m :=
  fun x => ExteriorAlgebra.map L.dualMap (ω (b + L x))

theorem pullA_isDeg {n : ℕ} {b : Fin m' → ℝ} {L : (Fin m → ℝ) →ₗ[ℝ] (Fin m' → ℝ)}
    (hA : ∀ x ∈ simplex m, b + L x ∈ simplex m') {ω : Ω m'} (h : IsDeg n ω) :
    IsDeg n (pullA b L ω) := fun x hx =>
  map_mem_exteriorPower _ (h _ (hA x hx))

/-- The coefficients of the pulled-back basis forms. -/
noncomputable def pcA (L : (Fin m → ℝ) →ₗ[ℝ] (Fin m' → ℝ)) (I : Finset (Fin m'))
    (J : Finset (Fin m)) : ℝ :=
  (formBasis m).repr (ExteriorAlgebra.map L.dualMap (formBasis m' I)) J

theorem coeff_pullA (b : Fin m' → ℝ) (L : (Fin m → ℝ) →ₗ[ℝ] (Fin m' → ℝ)) (ω : Ω m')
    (J : Finset (Fin m)) (x : Fin m → ℝ) :
    coeff (pullA b L ω) J x = ∑ I, coeff ω I (b + L x) * pcA L I J := by
  simp only [coeff, pullA, pcA]
  conv_lhs => rw [← (formBasis m').sum_repr (ω (b + L x))]
  simp only [map_sum, map_smul, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.smul_apply,
    smul_eq_mul]

theorem hasFDerivAt_aff (b : Fin m' → ℝ) (L : (Fin m → ℝ) →ₗ[ℝ] (Fin m' → ℝ)) (x : Fin m → ℝ) :
    HasFDerivAt (fun x => b + L x) (LinearMap.toContinuousLinearMap L) x :=
  (LinearMap.toContinuousLinearMap L).hasFDerivAt.const_add _

theorem contDiff_aff {n : WithTop ℕ∞} (b : Fin m' → ℝ) (L : (Fin m → ℝ) →ₗ[ℝ] (Fin m' → ℝ)) :
    ContDiff ℝ n (fun x => b + L x) :=
  contDiff_const.add (LinearMap.toContinuousLinearMap L).contDiff

theorem contDiffOn_coeff_pullA {b : Fin m' → ℝ} {L : (Fin m → ℝ) →ₗ[ℝ] (Fin m' → ℝ)}
    (hA : ∀ x ∈ simplex m, b + L x ∈ simplex m') {ω : Ω m'}
    (h : ∀ I, ContDiffOn ℝ r (coeff ω I) (simplex m')) (J : Finset (Fin m)) :
    ContDiffOn ℝ r (coeff (pullA b L ω) J) (simplex m) := by
  rw [show coeff (pullA b L ω) J = fun x => ∑ I, coeff ω I (b + L x) * pcA L I J from
    funext (coeff_pullA b L ω J)]
  exact ContDiffOn.sum fun I _ =>
    ((h I).comp (contDiff_aff b L).contDiffOn (fun x hx => hA x hx)).mul contDiffOn_const

theorem extD_pullA (hr : 1 ≤ r) {b : Fin m' → ℝ} {L : (Fin m → ℝ) →ₗ[ℝ] (Fin m' → ℝ)}
    (hA : ∀ x ∈ simplex m, b + L x ∈ simplex m') {ω : Ω m'}
    (hC : ∀ I, ContDiffOn ℝ r (coeff ω I) (simplex m')) {x : Fin m → ℝ}
    (hx : x ∈ simplex m) : extD (pullA b L ω) x = pullA b L (extD ω) x := by
  have hy : b + L x ∈ simplex m' := hA x hx
  have hd : ∀ I, HasFDerivWithinAt (coeff ω I)
      (fderivWithin ℝ (coeff ω I) (simplex m') (b + L x)) (simplex m') (b + L x) := fun I =>
    (((hC I).differentiableOn (by exact_mod_cast (show r ≠ 0 by omega))) _ hy).hasFDerivWithinAt
  have hpd : ∀ J (k : Fin m), fderivWithin ℝ (coeff (pullA b L ω) J) (simplex m) x (Pi.single k 1) =
      ∑ I, fderivWithin ℝ (coeff ω I) (simplex m') (b + L x) (L (Pi.single k 1)) * pcA L I J := by
    intro J k
    have e : coeff (pullA b L ω) J = fun x => ∑ I, coeff ω I (b + L x) * pcA L I J :=
      funext (coeff_pullA b L ω J)
    have hH : HasFDerivWithinAt (fun x => ∑ I, coeff ω I (b + L x) * pcA L I J)
        (∑ I, (pcA L I J) • ((fderivWithin ℝ (coeff ω I) (simplex m') (b + L x)).comp
          (LinearMap.toContinuousLinearMap L))) (simplex m) x := by
      refine HasFDerivWithinAt.fun_sum (u := Finset.univ) fun I _ => ?_
      exact ((hd I).comp x (hasFDerivAt_aff b L x).hasFDerivWithinAt
        (fun z hz => hA z hz)).mul_const (pcA L I J)
    rw [e, hH.fderivWithin (uniqueDiffOn_simplex m x hx)]
    simp [mul_comm]
  let T : (Fin m' → ℝ) →ₗ[ℝ] ExteriorAlgebra ℝ (Module.Dual ℝ (Fin m' → ℝ)) :=
    ∑ I, ((fderivWithin ℝ (coeff ω I) (simplex m') (b + L x) :
      (Fin m' → ℝ) →L[ℝ] ℝ) : (Fin m' → ℝ) →ₗ[ℝ] ℝ).smulRight (formBasis m' I)
  have hT : ∀ v, T v = ∑ I, fderivWithin ℝ (coeff ω I) (simplex m') (b + L x) v •
      formBasis m' I := by
    intro v; simp [T]
  have hR : pullA b L (extD ω) x = ExteriorAlgebra.map L.dualMap
      (∑ a, dx m' a * T (Pi.single a 1)) := by
    simp only [hT]; rfl
  rw [hR, wedge_natural]
  simp only [extD]
  refine Finset.sum_congr rfl fun k _ => ?_
  congr 1
  rw [hT]
  simp only [hpd, map_sum, map_smul, Finset.sum_smul, mul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun I _ => ?_
  rw [← Finset.smul_sum]
  congr 1
  exact (formBasis m).sum_repr _

theorem pullA_isCr (hr : 1 ≤ r) {b : Fin m' → ℝ} {L : (Fin m → ℝ) →ₗ[ℝ] (Fin m' → ℝ)}
    (hA : ∀ x ∈ simplex m, b + L x ∈ simplex m') {ω : Ω m'} (hC : IsCr r ω) :
    IsCr r (pullA b L ω) := fun J =>
  ⟨contDiffOn_coeff_pullA hA (fun I => (hC I).1) J,
    (contDiffOn_coeff_pullA hA (fun I => (hC I).2) J).congr fun x hx => by
      show (formBasis m).repr (extD (pullA b L ω) x) J = (formBasis m).repr (pullA b L (extD ω) x) J
      rw [extD_pullA hr hA (fun I => (hC I).1) hx]⟩

/-- Pullback is linear (pointwise, everywhere). -/
theorem pullA_add (b : Fin m' → ℝ) (L : (Fin m → ℝ) →ₗ[ℝ] (Fin m' → ℝ)) (ω ω' : Ω m') :
    pullA b L (ω + ω') = pullA b L ω + pullA b L ω' := by
  funext x; simp [pullA, map_add]

theorem pullA_smul (b : Fin m' → ℝ) (L : (Fin m → ℝ) →ₗ[ℝ] (Fin m' → ℝ)) (c : ℝ) (ω : Ω m') :
    pullA b L (c • ω) = c • pullA b L ω := by
  funext x; simp [pullA, map_smul]

/-- Functoriality: pulling back along `A ∘ B` is pulling back along `A`, then along `B`. -/
theorem pullA_comp {m'' : ℕ} (b : Fin m' → ℝ) (L : (Fin m → ℝ) →ₗ[ℝ] (Fin m' → ℝ))
    (b' : Fin m → ℝ) (L' : (Fin m'' → ℝ) →ₗ[ℝ] (Fin m → ℝ)) (ω : Ω m') :
    pullA b' L' (pullA b L ω) = pullA (b + L b') (L ∘ₗ L') ω := by
  funext x
  simp only [pullA, LinearMap.comp_apply, map_add, add_assoc]
  rw [← LinearMap.dualMap_comp_dualMap, ← ExteriorAlgebra.map_comp_map]
  rfl

/-- Pullback respects agreement on the simplex. -/
theorem pullA_congr {b : Fin m' → ℝ} {L : (Fin m → ℝ) →ₗ[ℝ] (Fin m' → ℝ)}
    (hA : ∀ x ∈ simplex m, b + L x ∈ simplex m') {ω ω' : Ω m'} (h : FormEqOn ω ω') :
    FormEqOn (pullA b L ω) (pullA b L ω') := fun x hx => by
  simp only [pullA, h _ (hA x hx)]

end PullAff

section PullS

/-! Simplicial pullbacks: the affine map `Δᵐ → Δᵐ'` sending the vertex `v_l` to `v_{θ l}` for any
`θ : Fin (m+1) → Fin (m'+1)` (cofaces, codegeneracies and the horn retractions), and functoriality. -/

variable {m m' r : ℕ}

/-- The linear part of the affine map with vertex images `w`. -/
noncomputable def affL (w : Fin (m + 1) → (Fin m' → ℝ)) : (Fin m → ℝ) →ₗ[ℝ] (Fin m' → ℝ) :=
  (Matrix.of fun (a : Fin m') (k : Fin m) => (w k.succ - w 0) a).mulVecLin

theorem affL_apply (w : Fin (m + 1) → (Fin m' → ℝ)) (x : Fin m → ℝ) :
    affL w x = ∑ k, x k • (w k.succ - w 0) := by
  funext a
  simp [affL, Matrix.mulVec, dotProduct, mul_comm]

theorem aff_vertex (w : Fin (m + 1) → (Fin m' → ℝ)) (l : Fin (m + 1)) :
    w 0 + affL w (vertex m l) = w l := by
  induction l using Fin.cases with
  | zero => simp [vertex]
  | succ k =>
    rw [affL_apply]
    simp [vertex, Pi.single_apply]

theorem aff_mem {w : Fin (m + 1) → (Fin m' → ℝ)} (hw : ∀ l, w l ∈ simplex m') :
    ∀ x ∈ simplex m, w 0 + affL w x ∈ simplex m' := by
  intro x hx
  let c : Fin (m + 1) → ℝ := Fin.cons (1 - ∑ k, x k) x
  have h0 : ∀ j ∈ (Finset.univ : Finset (Fin (m + 1))), 0 ≤ c j := by
    intro j _
    induction j using Fin.cases with
    | zero => simp only [c, Fin.cons_zero]; linarith [hx.2]
    | succ k => simp only [c, Fin.cons_succ]; exact hx.1 k
  have h1 : ∑ j, c j = 1 := by
    rw [Fin.sum_univ_succ]; simp only [c, Fin.cons_zero, Fin.cons_succ]; ring
  have hm := (convex_simplex m').sum_mem h0 h1 (z := w) (fun j _ => hw j)
  convert hm using 1
  rw [affL_apply, Fin.sum_univ_succ]
  simp only [c, Fin.cons_zero, Fin.cons_succ, smul_sub, Finset.sum_sub_distrib, sub_smul,
    one_smul, ← Finset.sum_smul]
  abel

/-- An affine map is determined by its vertex images. -/
theorem aff_ext {w : Fin (m + 1) → (Fin m' → ℝ)} {b : Fin m' → ℝ}
    {L : (Fin m → ℝ) →ₗ[ℝ] (Fin m' → ℝ)} (h : ∀ l, b + L (vertex m l) = w l) :
    b = w 0 ∧ L = affL w := by
  have hb : b = w 0 := by
    have := h 0
    simpa [vertex] using this
  refine ⟨hb, LinearMap.ext fun x => ?_⟩
  rw [linear_expand L x, linear_expand (affL w) x]
  refine Finset.sum_congr rfl fun a _ => ?_
  congr 1
  have h1 := h a.succ
  have h2 := aff_vertex w a.succ
  simp only [vertex, Fin.cases_succ] at h1 h2
  rw [hb] at h1
  exact add_left_cancel (h1.trans h2.symm)

/-- Pullback along the simplicial affine map with vertex map `θ`. -/
noncomputable def pullS (θ : Fin (m + 1) → Fin (m' + 1)) (ω : Ω m') : Ω m :=
  pullA (vertex m' (θ 0)) (affL fun l => vertex m' (θ l)) ω

theorem pull_eq_pullS (i : Fin (m + 2)) (ω : Ω (m + 1)) : pull m i ω = pullS i.succAbove ω := rfl

theorem pullS_mem (θ : Fin (m + 1) → Fin (m' + 1)) :
    ∀ x ∈ simplex m, vertex m' (θ 0) + (affL fun l => vertex m' (θ l)) x ∈ simplex m' :=
  aff_mem (w := fun l => vertex m' (θ l)) fun l => vertex_mem _ _

theorem pullS_comp {m'' : ℕ} (θ : Fin (m + 1) → Fin (m' + 1)) (θ' : Fin (m'' + 1) → Fin (m + 1))
    (ω : Ω m') : pullS θ' (pullS θ ω) = pullS (θ ∘ θ') ω := by
  simp only [pullS]
  rw [pullA_comp]
  obtain ⟨h1, h2⟩ := aff_ext (w := fun l => vertex m' (θ (θ' l)))
    (b := vertex m' (θ 0) + (affL fun l => vertex m' (θ l)) (vertex m (θ' 0)))
    (L := (affL fun l => vertex m' (θ l)) ∘ₗ (affL fun l => vertex m (θ' l))) (fun l => by
      rw [LinearMap.comp_apply, add_assoc, ← map_add,
        aff_vertex (fun l => vertex m (θ' l)) l, aff_vertex (fun l => vertex m' (θ l)) (θ' l)])
  rw [h1, h2]
  rfl

theorem pullS_isDeg {n : ℕ} (θ : Fin (m + 1) → Fin (m' + 1)) {ω : Ω m'} (h : IsDeg n ω) :
    IsDeg n (pullS θ ω) := pullA_isDeg (pullS_mem θ) h

theorem pullS_isCr (hr : 1 ≤ r) (θ : Fin (m + 1) → Fin (m' + 1)) {ω : Ω m'} (hC : IsCr r ω) :
    IsCr r (pullS θ ω) := pullA_isCr hr (pullS_mem θ) hC

theorem pullS_congr (θ : Fin (m + 1) → Fin (m' + 1)) {ω ω' : Ω m'} (h : FormEqOn ω ω') :
    FormEqOn (pullS θ ω) (pullS θ ω') := pullA_congr (pullS_mem θ) h

theorem pullS_id (ω : Ω m) : FormEqOn (pullS id ω) ω := fun x _ => by
  obtain ⟨h1, h2⟩ := aff_ext (w := fun l => vertex m (id l)) (b := 0)
    (L := LinearMap.id) (fun l => by simp)
  simp only [pullS, pullA]
  rw [← h1, ← h2]
  simp [LinearMap.dualMap_id, ExteriorAlgebra.map_id]

end PullS

section HornExt

/-! Horn filling for forms at the level of representatives (Lemma 5.9, surjectivity): the classical
inductive extension, correcting face by face with pullbacks along the retraction `retr i j` of
`Δᵐ⁺¹` onto its `i`-th face that moves the vertex `i` to the vertex `j`. -/

variable {m r : ℕ}

open Classical in
/-- The vertex map of the retraction onto the face `i` collapsing the vertex `i` onto `j`. -/
noncomputable def retr (i j : Fin (m + 2)) (k : Fin (m + 2)) : Fin (m + 1) :=
  if h : ∃ l, i.succAbove l = (if k = i then j else k) then h.choose else 0

theorem succAbove_retr {i j : Fin (m + 2)} (hij : j ≠ i) (k : Fin (m + 2)) :
    i.succAbove (retr i j k) = if k = i then j else k := by
  have hne : (if k = i then j else k) ≠ i := by
    split_ifs with h
    · exact hij
    · exact h
  have hex := Fin.exists_succAbove_eq hne
  rw [retr, dif_pos hex]
  exact hex.choose_spec

theorem retr_succAbove (i j : Fin (m + 2)) (l : Fin (m + 1)) : retr i j (i.succAbove l) = l := by
  have hne : i.succAbove l ≠ i := Fin.succAbove_ne i l
  have hex : ∃ l', i.succAbove l' = (if i.succAbove l = i then j else i.succAbove l) :=
    ⟨l, by rw [if_neg hne]⟩
  rw [retr, dif_pos hex]
  exact Fin.succAbove_right_injective (hex.choose_spec.trans (if_neg hne))

theorem retr_comp (i j : Fin (m + 2)) : retr i j ∘ i.succAbove = id :=
  funext (retr_succAbove i j)

theorem pullS_add' {m' : ℕ} (θ : Fin (m + 1) → Fin (m' + 1)) (ω ω' : Ω m') :
    pullS θ (ω + ω') = pullS θ ω + pullS θ ω' := pullA_add _ _ _ _

theorem pullS_sub {m' : ℕ} (θ : Fin (m + 1) → Fin (m' + 1)) (ω ω' : Ω m') :
    pullS θ (ω - ω') = pullS θ ω - pullS θ ω' := by
  funext x; simp [pullS, pullA, map_sub]

theorem isCr_sub (hr : 1 ≤ r) {ω ω' : Ω m} (h : IsCr r ω) (h' : IsCr r ω') : IsCr r (ω - ω') := by
  have e : ω - ω' = ω + (-1 : ℝ) • ω' := by funext x; simp [sub_eq_add_neg]
  rw [e]; exact isCr_add hr h (isCr_smul hr _ h')

theorem isDeg_sub {n : ℕ} {ω ω' : Ω m} (h : IsDeg n ω) (h' : IsDeg n ω') : IsDeg n (ω - ω') := by
  have e : ω - ω' = ω + (-1 : ℝ) • ω' := by funext x; simp [sub_eq_add_neg]
  rw [e]; exact isDeg_add h (isDeg_smul _ h')

/-- Strong compatibility of a horn tuple (`α j` is ignored): any two ways of seeing a simplex in two
faces give the same form. -/
def HornCompatF (j : Fin (m + 2)) (α : Fin (m + 2) → Ω m) : Prop :=
  ∀ i i' : Fin (m + 2), i ≠ j → i' ≠ j → ∀ (k : ℕ) (μ μ' : Fin (k + 1) → Fin (m + 1)),
    i.succAbove ∘ μ = i'.succAbove ∘ μ' → FormEqOn (pullS μ (α i)) (pullS μ' (α i'))

/-- `ω` extends the faces in `T`. -/
def ExtOn (α : Fin (m + 2) → Ω m) (T : Finset (Fin (m + 2))) (ω : Ω (m + 1)) : Prop :=
  ∀ i ∈ T, FormEqOn (pullS i.succAbove ω) (α i)

theorem retr_factor {i j t : Fin (m + 2)} (hij : i ≠ j) (hti : t ≠ i) (htj : t ≠ j) :
    ∃ μ' : Fin (m + 1) → Fin (m + 1), i.succAbove ∘ (retr i j ∘ t.succAbove) = t.succAbove ∘ μ' := by
  have hx : ∀ l, ∃ z, t.succAbove z = i.succAbove (retr i j (t.succAbove l)) := by
    intro l
    apply Fin.exists_succAbove_eq
    rw [succAbove_retr (Ne.symm hij)]
    split_ifs with h
    · exact Ne.symm htj
    · exact Fin.succAbove_ne t l
  choose μ' hμ' using hx
  exact ⟨μ', funext fun l => (hμ' l).symm⟩

/-- The extension formula itself (no regularity needed). -/
theorem ext_formula {j : Fin (m + 2)} {α : Fin (m + 2) → Ω m} (hc : HornCompatF j α)
    {T : Finset (Fin (m + 2))} (hT : j ∉ T) {i : Fin (m + 2)} (hij : i ≠ j) {ω : Ω (m + 1)}
    (hE : ExtOn α T ω) :
    ExtOn α (insert i T) (ω + pullS (retr i j) (α i - pullS i.succAbove ω)) := by
  intro t ht x hx
  have e1 : pullS t.succAbove (ω + pullS (retr i j) (α i - pullS i.succAbove ω)) x =
      pullS t.succAbove ω x + pullS (retr i j ∘ t.succAbove) (α i - pullS i.succAbove ω) x := by
    rw [pullS_add', pullS_comp]; rfl
  rw [e1]
  by_cases hti : t = i
  · subst hti
    rw [retr_comp, pullS_id _ x hx, Pi.sub_apply]
    abel
  · have htT : t ∈ T := (Finset.mem_insert.1 ht).resolve_left hti
    have htj : t ≠ j := fun h => hT (h ▸ htT)
    obtain ⟨μ', hμ'⟩ := retr_factor hij hti htj
    rw [pullS_sub, Pi.sub_apply, pullS_comp, hμ', ← pullS_comp t.succAbove μ',
      hc i t hij htj m (retr i j ∘ t.succAbove) μ' hμ' x hx, pullS_congr μ' (hE t htT) x hx,
      hE t htT x hx]
    abel

end HornExt

section HornJet

/-! Lemma 5.9 surjectivity at the jet level: a compatible tuple of jets (codim-2 identities only)
lifts to a strongly compatible tuple of representatives, which then fills. -/

variable {m r : ℕ}

/-- Cosimplicial identity `δ_a ∘ δ_b = δ_{b+1} ∘ δ_a` for `a ≤ b`. -/
theorem succAbove_succAbove_le {a b : Fin (m + 1)} (hab : a ≤ b) (l : Fin m) :
    a.castSucc.succAbove (b.succAbove l) = b.succ.succAbove (a.succAbove l) := by
  rw [Fin.le_def] at hab
  apply Fin.ext
  simp only [Fin.succAbove, Fin.lt_def]
  split_ifs <;> (try simp only [Fin.val_castSucc, Fin.val_succ, not_lt] at *) <;> omega

theorem factor_avoid {k : ℕ} {b : Fin (m + 1)} (μ : Fin (k + 1) → Fin (m + 1))
    (h : ∀ l, μ l ≠ b) : ∃ ν : Fin (k + 1) → Fin m, μ = b.succAbove ∘ ν := by
  choose ν hν using fun l => Fin.exists_succAbove_eq (h l)
  exact ⟨ν, funext fun l => (hν l).symm⟩

/-- The codimension-2 identities for representatives. -/
def HornPair (q : ℕ) (j : Fin (q + 3)) (α : Fin (q + 3) → Ω (q + 1)) : Prop :=
  ∀ a b : Fin (q + 2), a ≤ b → a.castSucc ≠ j → b.succ ≠ j →
    FormEqOn (pullS a.succAbove (α b.succ)) (pullS b.succAbove (α a.castSucc))

theorem hornCompatF_of_pair {q : ℕ} {j : Fin (q + 3)} {α : Fin (q + 3) → Ω (q + 1)}
    (hp : HornPair q j α) : HornCompatF j α := by
  have main : ∀ i i' : Fin (q + 3), i < i' → i ≠ j → i' ≠ j →
      ∀ (k : ℕ) (μ μ' : Fin (k + 1) → Fin (q + 2)),
      i.succAbove ∘ μ = i'.succAbove ∘ μ' → FormEqOn (pullS μ (α i)) (pullS μ' (α i')) := by
    intro i i' hlt hi hi' k μ μ' h
    obtain ⟨a, rfl⟩ : ∃ a : Fin (q + 2), a.castSucc = i :=
      ⟨i.castPred (Fin.ne_last_of_lt hlt), Fin.castSucc_castPred _ _⟩
    obtain ⟨b, rfl⟩ : ∃ b : Fin (q + 2), b.succ = i' :=
      ⟨i'.pred (Fin.ne_zero_of_lt hlt), Fin.succ_pred _ _⟩
    have hab : a ≤ b := Fin.castSucc_lt_succ_iff.mp hlt
    have e1 : a.castSucc.succAbove b = b.succ :=
      Fin.succAbove_of_le_castSucc _ _ (Fin.castSucc_le_castSucc_iff.mpr hab)
    have e2 : b.succ.succAbove a = a.castSucc :=
      Fin.succAbove_of_castSucc_lt _ _ (Fin.castSucc_lt_succ_iff.mpr hab)
    have hμ : ∀ l, μ l ≠ b := by
      intro l hl
      have e := congrFun h l
      simp only [Function.comp] at e
      rw [hl, e1] at e
      exact Fin.succAbove_ne _ _ e.symm
    have hμ' : ∀ l, μ' l ≠ a := by
      intro l hl
      have e := congrFun h l
      simp only [Function.comp] at e
      rw [hl, e2] at e
      exact Fin.succAbove_ne _ _ e
    obtain ⟨ν, rfl⟩ := factor_avoid μ hμ
    obtain ⟨ν', rfl⟩ := factor_avoid μ' hμ'
    have hνν : ν = ν' := funext fun l => by
      have e := congrFun h l
      simp only [Function.comp] at e
      rw [succAbove_succAbove_le hab] at e
      exact Fin.succAbove_right_injective (Fin.succAbove_right_injective e)
    subst hνν
    intro x hx
    rw [← pullS_comp, ← pullS_comp]
    exact (pullS_congr ν (hp a b hab hi hi') x hx).symm
  intro i i' hi hi' k μ μ' h
  rcases lt_trichotomy i i' with hlt | heq | hgt
  · exact main i i' hlt hi hi' k μ μ' h
  · subst heq
    have : μ = μ' := funext fun l => Fin.succAbove_right_injective (congrFun h l)
    subst this
    exact fun x _ => rfl
  · exact fun x hx => (main i' i hgt hi' hi k μ' μ h.symm x hx).symm

theorem hornCompatF_zero (j : Fin 2) (α : Fin 2 → Ω 0) : HornCompatF j α := by
  intro i i' hi hi' k μ μ' h
  have : i = i' := Fin.ext (by
    have := i.isLt; have := i'.isLt; have := j.isLt
    have h1 := Fin.val_ne_of_ne hi; have h2 := Fin.val_ne_of_ne hi'
    omega)
  subst this
  have : μ = μ' := funext fun l => Fin.succAbove_right_injective (congrFun h l)
  subst this
  exact fun x _ => rfl

theorem hornPair_of_jet (hr : 1 ≤ r) {q n : ℕ} {j : Fin (q + 3)} {α : Fin (q + 3) → Ω (q + 1)}
    (hα : ∀ i, IsDeg n (α i) ∧ IsCr r (α i))
    (x : {i : Fin (q + 3) // i ≠ j} → CrForms r (q + 1) n)
    (hx : ∀ i (hi : i ≠ j), (x ⟨i, hi⟩ : Jet r (q + 1) × Jet r (q + 1)) = jet r (α i))
    (hc : HornCompat (X := fun p => ↥(CrForms r p n)) (fun p => faceCr r p n) (q + 1) j x) : HornPair q j α := by
  have hc' : ∀ a b : Fin (q + 2), a ≤ b → ∀ (ha : a.castSucc ≠ j) (hb : b.succ ≠ j),
      faceCr r q n a (x ⟨b.succ, hb⟩) = faceCr r q n b (x ⟨a.castSucc, ha⟩) := hc
  intro a b hab ha hb
  have e := congrArg Subtype.val (hc' a b hab ha hb)
  have h1 : x ⟨b.succ, hb⟩ = ⟨jet r (α b.succ), hx _ hb ▸ (x ⟨b.succ, hb⟩).2⟩ :=
    Subtype.ext (hx _ hb)
  have h2 : x ⟨a.castSucc, ha⟩ = ⟨jet r (α a.castSucc), hx _ ha ▸ (x ⟨a.castSucc, ha⟩).2⟩ :=
    Subtype.ext (hx _ ha)
  rw [h1, h2, faceCr_eq hr a (hα _).1 (hα _).2, faceCr_eq hr b (hα _).1 (hα _).2] at e
  exact formEqOn_of_jet (pull_isCr hr a (hα _).2) (pull_isCr hr b (hα _).2) e

end HornJet

section Fold

/-! The horn-filling operator as an explicit fold (linear in the tuple, respects `FormEqOn`):
the input to the closed-graph argument for a continuous linear section. -/

variable {m r : ℕ}

noncomputable def foldE (j : Fin (m + 2)) (α : Fin (m + 2) → Ω m) :
    List (Fin (m + 2)) → Ω (m + 1)
  | [] => 0
  | i :: l => foldE j α l + pullS (retr i j) (α i - pullS i.succAbove (foldE j α l))

theorem pullS_smul' {m' : ℕ} (θ : Fin (m + 1) → Fin (m' + 1)) (c : ℝ) (ω : Ω m') :
    pullS θ (c • ω) = c • pullS θ ω := pullA_smul _ _ _ _

theorem foldE_ext {j : Fin (m + 2)} {α : Fin (m + 2) → Ω m} (hc : HornCompatF j α) :
    ∀ l : List (Fin (m + 2)), j ∉ l → ExtOn α l.toFinset (foldE j α l)
  | [], _ => fun i hi => by simp at hi
  | i :: l, hl => by
    have hij : i ≠ j := fun h => hl (h ▸ List.mem_cons_self ..)
    have hjl : j ∉ l := fun h => hl (List.mem_cons_of_mem _ h)
    rw [List.toFinset_cons]
    exact ext_formula hc (by simpa using hjl) hij (foldE_ext hc l hjl)

theorem foldE_reg (hr : 1 ≤ r) {n : ℕ} {j : Fin (m + 2)} {α : Fin (m + 2) → Ω m}
    (hα : ∀ i, IsDeg n (α i) ∧ IsCr r (α i)) :
    ∀ l : List (Fin (m + 2)), IsDeg n (foldE j α l) ∧ IsCr r (foldE j α l)
  | [] => ⟨isDeg_zero, isCr_zero⟩
  | i :: l => by
    obtain ⟨hD, hC⟩ := foldE_reg hr hα l
    exact ⟨isDeg_add hD (pullS_isDeg _ (isDeg_sub (hα i).1 (pullS_isDeg _ hD))),
      isCr_add hr hC (pullS_isCr hr _ (isCr_sub hr (hα i).2 (pullS_isCr hr _ hC)))⟩

theorem foldE_congr {j : Fin (m + 2)} {α α' : Fin (m + 2) → Ω m}
    (h : ∀ i, FormEqOn (α i) (α' i)) :
    ∀ l : List (Fin (m + 2)), FormEqOn (foldE j α l) (foldE j α' l)
  | [] => fun _ _ => rfl
  | i :: l => by
    have ih := foldE_congr (j := j) h l
    have h1 : FormEqOn (α i - pullS i.succAbove (foldE j α l))
        (α' i - pullS i.succAbove (foldE j α' l)) := fun y hy => by
      simp only [Pi.sub_apply]; rw [h i y hy, pullS_congr _ ih y hy]
    intro x hx
    simp only [foldE, Pi.add_apply]
    rw [ih x hx, pullS_congr _ h1 x hx]

theorem foldE_add (j : Fin (m + 2)) (α α' : Fin (m + 2) → Ω m) :
    ∀ l : List (Fin (m + 2)), foldE j (α + α') l = foldE j α l + foldE j α' l
  | [] => by simp [foldE]
  | i :: l => by
    simp only [foldE]
    rw [foldE_add j α α' l, pullS_add', Pi.add_apply,
      show α i + α' i - (pullS i.succAbove (foldE j α l) + pullS i.succAbove (foldE j α' l)) =
        (α i - pullS i.succAbove (foldE j α l)) + (α' i - pullS i.succAbove (foldE j α' l)) by abel,
      pullS_add']
    abel

theorem foldE_smul (j : Fin (m + 2)) (c : ℝ) (α : Fin (m + 2) → Ω m) :
    ∀ l : List (Fin (m + 2)), foldE j (c • α) l = c • foldE j α l
  | [] => by simp [foldE]
  | i :: l => by
    simp only [foldE]
    rw [foldE_smul j c α l, pullS_smul', Pi.smul_apply, ← smul_sub, pullS_smul', smul_add]

end Fold

section ClosedGraph

/-! Continuity of the face maps and of the horn section by the closed graph theorem: limits in the
jet space control the coefficients pointwise (order-0 jet components), and pullbacks / folds
preserve pointwise convergence of coefficients. -/

variable {m r : ℕ}

/-- Pointwise convergence of all coefficients on the simplex. -/
def CoeffTendsto (ωk : ℕ → Ω m) (ω : Ω m) : Prop :=
  ∀ I, ∀ x ∈ simplex m, Tendsto (fun k => coeff (ωk k) I x) atTop (𝓝 (coeff ω I x))

theorem coeffTendsto_pullS {m' : ℕ} (θ : Fin (m + 1) → Fin (m' + 1)) {ωk : ℕ → Ω m'}
    {ω : Ω m'} (h : CoeffTendsto ωk ω) :
    CoeffTendsto (fun k => pullS θ (ωk k)) (pullS θ ω) := by
  intro J x hx
  simp only [pullS, coeff_pullA]
  exact tendsto_finset_sum _ fun I _ => (h I _ (pullS_mem θ x hx)).mul_const _

theorem coeffTendsto_add {ωk ωk' : ℕ → Ω m} {ω ω' : Ω m} (h : CoeffTendsto ωk ω)
    (h' : CoeffTendsto ωk' ω') : CoeffTendsto (fun k => ωk k + ωk' k) (ω + ω') := by
  intro I x hx
  simp only [coeff_add, Pi.add_apply]
  exact (h I x hx).add (h' I x hx)

theorem coeffTendsto_sub {ωk ωk' : ℕ → Ω m} {ω ω' : Ω m} (h : CoeffTendsto ωk ω)
    (h' : CoeffTendsto ωk' ω') : CoeffTendsto (fun k => ωk k - ωk' k) (ω - ω') := by
  intro I x hx
  have e : ∀ (a b : Ω m), coeff (a - b) I x = coeff a I x - coeff b I x := fun a b => by
    simp [coeff]
  simp only [e]
  exact (h I x hx).sub (h' I x hx)

theorem coeffTendsto_foldE (j : Fin (m + 2)) {αk : ℕ → Fin (m + 2) → Ω m}
    {α : Fin (m + 2) → Ω m} (h : ∀ i, CoeffTendsto (fun k => αk k i) (α i)) :
    ∀ l : List (Fin (m + 2)), CoeffTendsto (fun k => foldE j (αk k) l) (foldE j α l)
  | [] => fun I x _ => by simp only [foldE]; exact tendsto_const_nhds
  | i :: l => by
    have ih := coeffTendsto_foldE j h l
    simp only [foldE]
    exact coeffTendsto_add ih (coeffTendsto_pullS _ (coeffTendsto_sub (h i)
      (coeffTendsto_pullS _ ih)))

theorem coeffTendsto_of_jet {ωk : ℕ → Ω m} {ω : Ω m} (hk : ∀ k, IsCr r (ωk k)) (hω : IsCr r ω)
    (h : Tendsto (fun k => jet r (ωk k)) atTop (𝓝 (jet r ω))) : CoeffTendsto ωk ω := by
  intro I x hx
  let j0 : Fin (r + 1) := 0
  have hj0 : (j0 : ℕ) = 0 := rfl
  have β0 : Fin (j0 : ℕ) → Fin m := fun l => absurd l.isLt (by simp [j0])
  have hc : Continuous (fun w : Jet r m × Jet r m => w.1 I j0 β0 ⟨x, hx⟩) :=
    (continuous_eval_const _).comp
      ((continuous_jet_eval I j0 β0).comp continuous_fst)
  have t := (hc.tendsto _).comp h
  have e1 : (jet r ω).1 I j0 β0 ⟨x, hx⟩ = coeff ω I x := jetComp_zero (hω I).1 hj0 β0 hx
  rw [Function.comp_def, e1] at t
  exact t.congr fun k => jetComp_zero ((hk k) I).1 hj0 β0 hx

theorem coeffTendsto_unique {ωk : ℕ → Ω m} {a b : Ω m} (h1 : CoeffTendsto ωk a)
    (h2 : CoeffTendsto ωk b) : FormEqOn a b := fun x hx =>
  (formBasis m).ext_elem fun I => tendsto_nhds_unique (h1 I x hx) (h2 I x hx)

theorem exists_rep (hr : 1 ≤ r) {n : ℕ} (w : CrForms r m n) :
    ∃ ω : Ω m, (IsDeg n ω ∧ IsCr r ω) ∧ jet r ω = w := by
  have := w.2
  rw [← SetLike.mem_coe, crForms_eq_image hr n] at this
  exact this

open BoundedContinuousFunction in
theorem jet_complete (r m : ℕ) : CompleteSpace (Jet r m × Jet r m) := by
  have : CompleteSpace (Jet r m) := inferInstanceAs (CompleteSpace ((I : Finset (Fin m)) →
    (k : Fin (r + 1)) → (Fin (k : ℕ) → Fin m) → (simplex m →ᵇ ℝ)))
  infer_instance

theorem crForms_complete (r m n : ℕ) : CompleteSpace (CrForms r m n) := by
  haveI := jet_complete r m
  exact (Submodule.isClosed_topologicalClosure _).completeSpace_coe

theorem faceCr_val (hr : 1 ≤ r) {n : ℕ} (i : Fin (m + 2)) (w : CrForms r (m + 1) n)
    {ω : Ω (m + 1)} (hD : IsDeg n ω) (hC : IsCr r ω) (h : jet r ω = w) :
    (faceCr r m n i w : Jet r m × Jet r m) = jet r (pull m i ω) := by
  obtain ⟨w, hw⟩ := w
  simp only at h
  subst h
  exact faceCr_eq hr i hD hC hw

/-- The face map `dᵢ` on `Ωⁿ_{Cʳ}` as a linear map. -/
noncomputable def faceLin (hr : 1 ≤ r) (n : ℕ) (i : Fin (m + 2)) :
    CrForms r (m + 1) n →ₗ[ℝ] CrForms r m n where
  toFun := faceCr r m n i
  map_add' w w' := by
    obtain ⟨ω, hω, h⟩ := exists_rep hr w
    obtain ⟨ω', hω', h'⟩ := exists_rep hr w'
    apply Subtype.ext
    rw [Submodule.coe_add, faceCr_val hr i (w + w') (isDeg_add hω.1 hω'.1) (isCr_add hr hω.2 hω'.2)
      (by rw [jet_add hr hω.2 hω'.2, h, h']; rfl), faceCr_val hr i w hω.1 hω.2 h,
      faceCr_val hr i w' hω'.1 hω'.2 h', pull_eq_pullS, pull_eq_pullS, pull_eq_pullS, pullS_add',
      jet_add hr (pullS_isCr hr _ hω.2) (pullS_isCr hr _ hω'.2)]
  map_smul' c w := by
    obtain ⟨ω, hω, h⟩ := exists_rep hr w
    apply Subtype.ext
    rw [Submodule.coe_smul, faceCr_val hr i (c • w) (isDeg_smul c hω.1) (isCr_smul hr c hω.2)
      (by rw [jet_smul hr c hω.2, h]; rfl), faceCr_val hr i w hω.1 hω.2 h, pull_eq_pullS,
      pull_eq_pullS, pullS_smul', jet_smul hr c (pullS_isCr hr _ hω.2)]
    rfl

end ClosedGraph

section HornSection

/-! The continuous linear horn section `E` (fold of retraction pullbacks on representatives),
the simplicial identities for `faceCr`, and Lemma 5.9 for `Ωⁿ_{Cʳ}`. -/

variable {m r : ℕ}

open Classical in
noncomputable def rep (n : ℕ) (j : Fin (m + 2))
    (y : {i : Fin (m + 2) // i ≠ j} → CrForms r m n) (i : Fin (m + 2)) : Ω m :=
  if hi : i ≠ j then
    (if h : ∃ ω : Ω m, (IsDeg n ω ∧ IsCr r ω) ∧ jet r ω = y ⟨i, hi⟩ then h.choose else 0)
  else 0

theorem rep_spec {n : ℕ} {j : Fin (m + 2)} (y : {i : Fin (m + 2) // i ≠ j} → CrForms r m n)
    (i : Fin (m + 2)) : IsDeg n (rep n j y i) ∧ IsCr r (rep n j y i) := by
  unfold rep
  split_ifs with hi h
  · exact h.choose_spec.1
  · exact ⟨isDeg_zero, isCr_zero⟩
  · exact ⟨isDeg_zero, isCr_zero⟩

theorem rep_jet (hr : 1 ≤ r) {n : ℕ} {j : Fin (m + 2)}
    (y : {i : Fin (m + 2) // i ≠ j} → CrForms r m n) {i : Fin (m + 2)} (hi : i ≠ j) :
    jet r (rep n j y i) = y ⟨i, hi⟩ := by
  have hex := exists_rep hr (y ⟨i, hi⟩)
  unfold rep
  rw [dif_pos hi, dif_pos hex]
  exact hex.choose_spec.2

theorem rep_self {n : ℕ} {j : Fin (m + 2)} (y : {i : Fin (m + 2) // i ≠ j} → CrForms r m n) :
    rep n j y j = 0 := by
  unfold rep
  rw [dif_neg (not_not.mpr rfl)]

noncomputable def hornList (j : Fin (m + 2)) : List (Fin (m + 2)) := (Finset.univ.erase j).toList

theorem not_mem_hornList (j : Fin (m + 2)) : j ∉ hornList j := by simp [hornList]

theorem hornList_toFinset (j : Fin (m + 2)) : (hornList j).toFinset = Finset.univ.erase j := by
  simp [hornList]

/-- The horn section `E : ∏_{i ≠ j} Ωⁿ(Δᵐ) → Ωⁿ(Δᵐ⁺¹)`. -/
noncomputable def secLin (hr : 1 ≤ r) (n : ℕ) (j : Fin (m + 2)) :
    ((i : {i : Fin (m + 2) // i ≠ j}) → CrForms r m n) →ₗ[ℝ] CrForms r (m + 1) n where
  toFun y := ⟨jet r (foldE j (rep n j y) (hornList j)), by
    rw [← SetLike.mem_coe, crForms_eq_image hr n]
    exact ⟨_, foldE_reg hr (rep_spec y) _, rfl⟩⟩
  map_add' y y' := by
    have hcon : ∀ i, FormEqOn (rep n j (y + y') i) ((rep n j y + rep n j y') i) := by
      intro i
      by_cases hi : i ≠ j
      · refine formEqOn_of_jet (rep_spec _ i).2
          (isCr_add hr (rep_spec y i).2 (rep_spec y' i).2) ?_
        rw [Pi.add_apply, jet_add hr (rep_spec y i).2 (rep_spec y' i).2, rep_jet hr _ hi,
          rep_jet hr _ hi, rep_jet hr _ hi]
        rfl
      · rw [not_not] at hi
        subst hi
        rw [Pi.add_apply, rep_self, rep_self, rep_self, add_zero]
        exact fun _ _ => rfl
    apply Subtype.ext
    show jet r (foldE j (rep n j (y + y')) (hornList j)) =
      jet r (foldE j (rep n j y) (hornList j)) + jet r (foldE j (rep n j y') (hornList j))
    rw [jet_congr (foldE_congr (j := j) hcon _), foldE_add,
      jet_add hr (foldE_reg hr (rep_spec y) _).2 (foldE_reg hr (rep_spec y') _).2]
  map_smul' c y := by
    have hcon : ∀ i, FormEqOn (rep n j (c • y) i) ((c • rep n j y) i) := by
      intro i
      by_cases hi : i ≠ j
      · refine formEqOn_of_jet (rep_spec _ i).2 (isCr_smul hr c (rep_spec y i).2) ?_
        rw [Pi.smul_apply, jet_smul hr c (rep_spec y i).2, rep_jet hr _ hi, rep_jet hr _ hi]
        rfl
      · rw [not_not] at hi
        subst hi
        rw [Pi.smul_apply, rep_self, rep_self, smul_zero]
        exact fun _ _ => rfl
    apply Subtype.ext
    show jet r (foldE j (rep n j (c • y)) (hornList j)) =
      c • jet r (foldE j (rep n j y) (hornList j))
    rw [jet_congr (foldE_congr (j := j) hcon _), foldE_smul,
      jet_smul hr c (foldE_reg hr (rep_spec y) _).2]

theorem secLin_continuous (hr : 1 ≤ r) (n : ℕ) (j : Fin (m + 2)) :
    Continuous (secLin (r := r) hr n j) := by
  haveI := crForms_complete r m n
  haveI := crForms_complete r (m + 1) n
  refine (secLin hr n j).continuous_of_seq_closed_graph fun u y z hu hz => ?_
  obtain ⟨ωz, hωz, hzj⟩ := exists_rep hr z
  have t1 : CoeffTendsto (fun k => foldE j (rep n j (u k)) (hornList j)) ωz := by
    refine coeffTendsto_of_jet (fun k => (foldE_reg hr (rep_spec (u k)) _).2) hωz.2 ?_
    have := (continuous_subtype_val.tendsto z).comp hz
    rw [hzj]
    exact this
  have t2 : CoeffTendsto (fun k => foldE j (rep n j (u k)) (hornList j))
      (foldE j (rep n j y) (hornList j)) := by
    refine coeffTendsto_foldE j (fun i => ?_) _
    by_cases hi : i ≠ j
    · refine coeffTendsto_of_jet (fun k => (rep_spec (u k) i).2) (rep_spec y i).2 ?_
      have e : (fun k => jet r (rep n j (u k) i)) =
          fun k => ((u k ⟨i, hi⟩ : CrForms r m n) : Jet r m × Jet r m) :=
        funext fun k => rep_jet hr _ hi
      rw [e, rep_jet hr _ hi]
      exact (continuous_subtype_val.tendsto _).comp (((continuous_apply _).tendsto _).comp hu)
    · rw [not_not] at hi
      subst hi
      intro I x _
      simp only [rep_self]
      exact tendsto_const_nhds
  apply Subtype.ext
  rw [← hzj]
  exact jet_congr (coeffTendsto_unique t1 t2)

theorem secLin_spec (hr : 1 ≤ r) {n : ℕ} (j : Fin (m + 2))
    (y : {i : Fin (m + 2) // i ≠ j} → CrForms r m n)
    (hc : HornCompat (X := fun p => ↥(CrForms r p n)) (fun p => faceCr r p n) m j y) :
    hornMap (X := fun p => ↥(CrForms r p n)) (fun p => faceCr r p n) m j (secLin hr n j y) = y := by
  have hα := rep_spec (n := n) y
  have hx : ∀ i (hi : i ≠ j), (y ⟨i, hi⟩ : Jet r m × Jet r m) = jet r (rep n j y i) :=
    fun i hi => (rep_jet hr y hi).symm
  have hF : HornCompatF j (rep n j y) := by
    rcases m with _ | q
    · exact hornCompatF_zero j _
    · exact hornCompatF_of_pair (hornPair_of_jet hr hα y hx hc)
  have hE := foldE_ext hF (hornList j) (not_mem_hornList j)
  rw [hornList_toFinset] at hE
  have hreg := foldE_reg hr hα (j := j) (hornList j)
  funext i
  apply Subtype.ext
  show (faceCr r m n i.1 (secLin hr n j y) : Jet r m × Jet r m) = y i
  rw [faceCr_val hr i.1 (secLin hr n j y) hreg.1 hreg.2 rfl]
  exact (jet_congr (hE i.1 (by simp [i.2]))).trans (hx i.1 i.2).symm

/-- Simplicial identity `dₐ d_{b+1} = d_b dₐ` (`a ≤ b`) for `faceCr`. -/
theorem faceCr_faceCr (hr : 1 ≤ r) {n : ℕ} {a b : Fin (m + 2)} (hab : a ≤ b)
    (w : CrForms r (m + 2) n) :
    faceCr r m n a (faceCr r (m + 1) n b.succ w) = faceCr r m n b (faceCr r (m + 1) n a.castSucc w) := by
  obtain ⟨ω, hω, h⟩ := exists_rep hr w
  apply Subtype.ext
  rw [faceCr_val hr a _ (pull_isDeg _ hω.1) (pull_isCr hr _ hω.2)
      (faceCr_val hr b.succ w hω.1 hω.2 h).symm,
    faceCr_val hr b _ (pull_isDeg _ hω.1) (pull_isCr hr _ hω.2)
      (faceCr_val hr a.castSucc w hω.1 hω.2 h).symm]
  simp only [pull_eq_pullS, pullS_comp]
  rw [show b.succ.succAbove ∘ a.succAbove = a.castSucc.succAbove ∘ b.succAbove from
    funext fun l => (succAbove_succAbove_le hab l).symm]

end HornSection

section Lemma59

/-! Lemma 5.9 for `Ωⁿ_{Cʳ}(Δ^•)`: horn sets are closed complemented subspaces (the range of the
continuous projection `hornMap ∘ E`), and `hornMap` is a surjective submersion with the affine
  right inverse `y ↦ x + E (y - hornMap x)`. -/

variable {m r : ℕ}

noncomputable def secCLM (hr : 1 ≤ r) (n : ℕ) (j : Fin (m + 2)) :
    ((i : {i : Fin (m + 2) // i ≠ j}) → CrForms r m n) →L[ℝ] CrForms r (m + 1) n :=
  ⟨secLin hr n j, secLin_continuous hr n j⟩

end Lemma59

section Lemma59Closed

/-! Lemma 5.9 for closed forms `Ωⁿ_closed(Δ^•)`: same argument with closed representatives. -/

variable {m r : ℕ}

end Lemma59Closed

end IntLInfty.Kan.A83

/-! a83e3b53 relay 8: regularity of the cone integral `x ↦ ∫₀¹ tᵖ • f (t • x) dt` within a compact
convex set containing `0` (the analytic core of the Poincare homotopy operator on the simplex). -/

set_option autoImplicit false

namespace IntLInfty.Kan.A83Cone

open Set Filter Topology

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

variable {S : Set E}

end IntLInfty.Kan.A83Cone

/-! a83e3b53 relay 9: the Poincare identity `d (K β) = β` for the cone homotopy operator
`K β x = ι_x (∫₀¹ tⁿ β (t x) dt)` on closed `(n+1)`-forms, coordinate free (interior product =
`CliffordAlgebra.contractLeft`). The exterior algebra gets the norm transported from its basis. -/

namespace IntLInfty.Kan.A83Poinc

open IntLInfty.Kan IntLInfty.Kan.A83Cone

section generic

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {S : Set E}

end generic

end IntLInfty.Kan.A83Poinc

/-! ## Part 2 (relay 10): rep-level horn filling with prescribed exterior derivative
(Lemma 5.11 surjectivity / the fibrewise filling step of K1): a horn of `n`-forms `αᵢ` and a closed
`(n+1)`-form `β` on `Δᵐ⁺¹` with `dαᵢ = dᵢ β` extend to an `n`-form `ω` with `dᵢ ω = αᵢ`, `dω = β`.
Construction: `ω = K β + γ`, `γ` a closed filler of the closed horn `αᵢ - dᵢ (K β)`. -/

namespace IntLInfty.Kan.A83Fill

open IntLInfty.Kan IntLInfty.Kan.A83 IntLInfty.Kan.A83Poinc

variable {m r : ℕ}

end IntLInfty.Kan.A83Fill

/-! ## Part 3 (relay 10): graphs of smooth maps are split submanifolds (tool for K0b).
`M = {x | x = P x + g x}` for a continuous idempotent `P` and a `C^∞` map `g` with `g ∘ P = g`,
`P ∘ g = 0`: the global chart `x ↦ x - g x` (inverse `y ↦ y + g y`) carries `M` onto `range P`. -/

namespace IntLInfty.Kan.A83Graph

open IntLInfty.Kan
open scoped ContDiff

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

end IntLInfty.Kan.A83Graph

namespace IntLInfty.Kan.A83Graph

open IntLInfty.Kan
open scoped ContDiff

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

end IntLInfty.Kan.A83Graph

/-! ## Relay 12: `CrClosed` is complemented in `CrForms`. The projection is `w ↦ w - jet (K (d ω))`
for any representative `ω` of `w`, where `K` is the cone (Poincaré) operator. -/

namespace IntLInfty.Kan.A83Proj

open IntLInfty.Kan IntLInfty.Kan.A83 IntLInfty.Kan.A83Cone IntLInfty.Kan.A83Poinc
open Filter Topology
open scoped BoundedContinuousFunction


variable {m r : ℕ}

end IntLInfty.Kan.A83Proj

/-! ## Relay 12 (b): graded Leibniz rule for `extD` and `Cʳ` products (step (3) groundwork). -/

namespace IntLInfty.Kan.A83Leib

open IntLInfty.Kan IntLInfty.Kan.A83 IntLInfty.Kan.A83Poinc


variable {m : ℕ}

end IntLInfty.Kan.A83Leib

namespace IntLInfty.Kan.A83DGA

open IntLInfty.Kan

section Ext

variable {V : Type} [AddCommGroup V] [Module ℝ V]

end Ext

section Lift

variable {m : ℕ} {L : ℕ → Type} [∀ i, AddCommGroup (L i)] [∀ i, Module ℝ (L i)]

end Lift

end IntLInfty.Kan.A83DGA

/-! Relay 13: the DGA condition for `ceLift` reduces to generators (step 3b part 2). -/

namespace IntLInfty.Kan.A83DGA

open IntLInfty.Kan IntLInfty.Kan.A83 IntLInfty.Kan.A83Leib IntLInfty.Kan.A83Proj

variable {m : ℕ} {L : ℕ → Type} [∀ i, AddCommGroup (L i)] [∀ i, Module ℝ (L i)]

end IntLInfty.Kan.A83DGA

/-! Relay 13: uniqueness on `A_S` and normalisation of generator values (cut off the simplex). -/

namespace IntLInfty.Kan.A83DGA

open IntLInfty.Kan IntLInfty.Kan.A83

variable {m : ℕ} {L : ℕ → Type} [∀ i, AddCommGroup (L i)] [∀ i, Module ℝ (L i)]

end IntLInfty.Kan.A83DGA

/-! ## (3c) δ-closure of the Postnikov generator algebras: `genAlg (tauLt n)` -/

namespace IntLInfty.Kan.A83Tau

open IntLInfty.Kan IntLInfty.Kan.A83

variable {L : ℕ → Type} [∀ i, AddCommGroup (L i)] [∀ i, Module ℝ (L i)]

end IntLInfty.Kan.A83Tau

/-! ## (3c) detection homomorphisms: freeness facts about `C∗(L)` needed for the `τ≤n` half -/

namespace IntLInfty.Kan.A83Det

open IntLInfty.Kan IntLInfty.Kan.A83
open scoped TensorProduct

variable {L : ℕ → Type} [∀ i, AddCommGroup (L i)] [∀ i, Module ℝ (L i)]

section Lift

variable {A : Type} [Ring A] [Algebra ℝ A]

end Lift

section OddTop

end OddTop

/-! ### even top index: target `ExteriorAlgebra ℝ (Fin 2 → ℝ)` -/

section EvenTop

end EvenTop

end IntLInfty.Kan.A83Det

/-! ## (3c) second half: `genAlg (tauLe n)` is `δ`-closed -/

namespace IntLInfty.Kan.A83TauLe

open IntLInfty.Kan IntLInfty.Kan.A83 IntLInfty.Kan.A83Tau
open scoped TensorProduct

variable {L : ℕ → Type} [∀ i, AddCommGroup (L i)] [∀ i, Module ℝ (L i)]

end IntLInfty.Kan.A83TauLe

namespace IntLInfty.Kan.A83Wedge

/-! Relay 16: the wedge product on `Ω_{Cʳ}` is a continuous bilinear map
`CrForms r m p × CrForms r m q → CrForms r m (p + q)` (closed graph in each variable, then closed
graph for the outer map into the operator space), hence `C^∞`. -/

open IntLInfty.Kan IntLInfty.Kan.A83 IntLInfty.Kan.A83Leib Filter Topology
open scoped ContDiff

variable {m r : ℕ}

/-- A chosen representative form of a point of `Ωⁿ_{Cʳ}(Δᵐ)`. -/
noncomputable def wRep (hr : 1 ≤ r) {n : ℕ} (w : CrForms r m n) : Ω m :=
  (exists_rep hr w).choose

theorem wRep_spec (hr : 1 ≤ r) {n : ℕ} (w : CrForms r m n) :
    (IsDeg n (wRep hr w) ∧ IsCr r (wRep hr w)) ∧ jet r (wRep hr w) = w :=
  (exists_rep hr w).choose_spec

end IntLInfty.Kan.A83Wedge

/-! ## Relay 17: cone Gronwall (Volterra uniqueness along rays). If `‖B x‖ ≤ C ‖x‖ ∫₀¹ ‖B (t x)‖ dt`
on a star-shaped set and `B` is bounded and continuous there, then `B = 0`. This is the uniqueness
step for the K0b characterization `H z = K N(z) ↔ d z = N(z)` (the defect `B = dz - N z` satisfies
`B = K (linear in B)` by `δ² = 0`). -/

namespace IntLInfty.Kan.A83Gron

open intervalIntegral

end IntLInfty.Kan.A83Gron

/-! Relay 18 (K0b step 2): jet-level evaluation of generator lifts is `C^∞` in the generator data.
`SmoothFam r n F`: `z ↦ F z` is a family of `Cʳ` `n`-forms whose jets depend smoothly on `z`.
Closed under `+`, scalars, finite sums, wedge, constants, congruence on `Δᵐ`; `ceLift` of smooth
generator data sends every element of `A_S` to a finite sum of smooth homogeneous families, and a
pointwise-homogeneous such sum is itself a smooth family (graded decomposition of `⋀`). -/

namespace IntLInfty.Kan.A83Ev

open IntLInfty.Kan IntLInfty.Kan.A83 IntLInfty.Kan.A83Leib IntLInfty.Kan.A83DGA
  IntLInfty.Kan.A83Wedge IntLInfty.Kan.A83Proj
open scoped ContDiff

section Fam

variable {m r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

end Fam

section Lift

variable {m r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {L : ℕ → Type} [∀ i, AddCommGroup (L i)] [∀ i, Module ℝ (L i)]

end Lift

end IntLInfty.Kan.A83Ev

/-! Relay 18 (K0b step 2, concrete data): generator values `Φ_z` read off a point `z` of the
ambient space `Amb r S m`, and `z ↦ jet (Φ_z x)` is `C^∞`. -/

namespace IntLInfty.Kan.A83Ev

open IntLInfty.Kan IntLInfty.Kan.A83 IntLInfty.Kan.A83Leib IntLInfty.Kan.A83DGA
  IntLInfty.Kan.A83Wedge IntLInfty.Kan.A83Proj
open scoped ContDiff

section AmbVal

variable {m r : ℕ} {L : ℕ → Type} [∀ i, AddCommGroup (L i)] [∀ i, Module ℝ (L i)]
  [∀ i, FiniteDimensional ℝ (L i)]

/-- A chosen linear retraction onto `S i`. -/
noncomputable def retr (S : GenSys L) (i : ℕ) : Module.Dual ℝ (L i) →ₗ[ℝ] S i :=
  (LinearMap.exists_leftInverse_of_injective (K := ℝ) (V := S i) (V' := Module.Dual ℝ (L i))
    (S i).subtype (Submodule.ker_subtype _)).choose

theorem retr_spec (S : GenSys L) (i : ℕ) (ξ : S i) : retr S i (ξ : Module.Dual ℝ (L i)) = ξ :=
  LinearMap.congr_fun
    (LinearMap.exists_leftInverse_of_injective (K := ℝ) (V := S i) (V' := Module.Dual ℝ (L i))
      (S i).subtype (Submodule.ker_subtype _)).choose_spec ξ

end AmbVal

end IntLInfty.Kan.A83Ev

/-! ## Relay 19: K0b step (3), generic part. Defect bound for an algebra map (the defect
`D a = d Φ a - Φ (δ a)` is a Φ-derivation, so it is pointwise bounded by the generator defects), the
cone-operator norm bound, and the Gronwall vanishing of a family of forms with `K B = 0` and
`|dB| ≤ C |B|`. -/

namespace IntLInfty.Kan.A83Defect

open IntLInfty.Kan IntLInfty.Kan.A83 IntLInfty.Kan.A83Cone IntLInfty.Kan.A83Poinc
  IntLInfty.Kan.A83Proj IntLInfty.Kan.A83Leib IntLInfty.Kan.A83DGA


variable {m r : ℕ}

variable {L : ℕ → Type} [∀ i, AddCommGroup (L i)] [∀ i, Module ℝ (L i)]

end IntLInfty.Kan.A83Defect

/-! ## Relay 20: K0b step (3), concrete: `integ_of_K`. A point `z` of the ambient space whose
generator defects `d Φ_z(ξ) - Φ_z(δ ξ)` are killed by the cone operator lies in `∫_S`. -/

namespace IntLInfty.Kan.A83Defect

theorem extPow_eq_zero_of_lt {V : Type} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    {p : ℕ} (hp : Module.finrank ℝ V < p) {a : ExteriorAlgebra ℝ V} (ha : a ∈ ⋀[ℝ]^p V) :
    a = 0 := by
  rw [← ExteriorAlgebra.ιMulti_span_fixedDegree] at ha
  induction ha using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨v, rfl⟩ := hy
    apply AlternatingMap.map_linearDependent
    intro hli
    have := hli.fintype_card_le_finrank
    simp at this
    omega
  | zero => rfl
  | add x y _ _ hx hy => rw [hx, hy, add_zero]
  | smul c x _ hx => rw [hx, smul_zero]

end IntLInfty.Kan.A83Defect

namespace IntLInfty.Kan.A83IntegK

open IntLInfty.Kan IntLInfty.Kan.A83 IntLInfty.Kan.A83Poinc IntLInfty.Kan.A83Proj
  IntLInfty.Kan.A83Leib IntLInfty.Kan.A83DGA IntLInfty.Kan.A83Ev IntLInfty.Kan.A83Defect


variable {m r : ℕ} {L : ℕ → Type} [∀ i, AddCommGroup (L i)] [∀ i, Module ℝ (L i)]

variable [∀ i, FiniteDimensional ℝ (L i)]

end IntLInfty.Kan.A83IntegK

/-! ## Relay 20: K0b (⊆): a point of `∫_S` has vanishing basis-generator defects. -/

namespace IntLInfty.Kan.A83IntegK

open IntLInfty.Kan IntLInfty.Kan.A83 IntLInfty.Kan.A83Poinc IntLInfty.Kan.A83Proj
  IntLInfty.Kan.A83Leib IntLInfty.Kan.A83DGA IntLInfty.Kan.A83Ev IntLInfty.Kan.A83Defect


variable {m r : ℕ} {L : ℕ → Type} [∀ i, AddCommGroup (L i)] [∀ i, Module ℝ (L i)]
  [∀ i, FiniteDimensional ℝ (L i)]

end IntLInfty.Kan.A83IntegK

namespace IntLInfty.Kan.A83Top

open IntLInfty.Kan
open scoped TensorProduct

variable {L : ℕ → Type} [∀ i, AddCommGroup (L i)] [∀ i, Module ℝ (L i)]

variable [∀ i, FiniteDimensional ℝ (L i)]

end IntLInfty.Kan.A83Top

namespace IntLInfty.Kan.A83IFT

open IntLInfty.Kan
open scoped ContDiff

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

end IntLInfty.Kan.A83IFT

/-! Relay 22 (K0b-i): `K ∘ K = 0`, `d K + K d = 1` consequences for non-closed `Cʳ` forms,
and the sup-norm of a form is bounded by its `Cʳ` jet norm. -/
namespace IntLInfty.Kan.A83KK

open IntLInfty.Kan IntLInfty.Kan.A83 IntLInfty.Kan.A83Cone IntLInfty.Kan.A83Poinc
  IntLInfty.Kan.A83Proj
open Filter Topology
open scoped BoundedContinuousFunction


variable {m r : ℕ}

end IntLInfty.Kan.A83KK

/-! ### K0b-i: the cone operator `K` and `d` as continuous linear maps on `Ωⁿ_{Cʳ}`. -/

namespace IntLInfty.Kan.A83KL

open IntLInfty.Kan IntLInfty.Kan.A83 IntLInfty.Kan.A83Cone IntLInfty.Kan.A83Poinc
  IntLInfty.Kan.A83Proj IntLInfty.Kan.A83KK
open Filter Topology
open scoped BoundedContinuousFunction


variable {m r : ℕ}

end IntLInfty.Kan.A83KL

/-! ### K0b-ii: the map `G z = jet K(Φ_z(δ b))` on `Amb` is `C^∞`. -/

namespace IntLInfty.Kan.A83G

open IntLInfty.Kan IntLInfty.Kan.A83 IntLInfty.Kan.A83Cone IntLInfty.Kan.A83Poinc
  IntLInfty.Kan.A83Proj IntLInfty.Kan.A83KK IntLInfty.Kan.A83KL IntLInfty.Kan.A83Ev
  IntLInfty.Kan.A83IntegK
open scoped ContDiff


variable {m r : ℕ} {L : ℕ → Type} [∀ i, AddCommGroup (L i)] [∀ i, Module ℝ (L i)]
  [∀ i, FiniteDimensional ℝ (L i)]

end IntLInfty.Kan.A83G

/-! ### K0b-iii (1): coordinatewise `H` on `Amb` and `∫_S = {z | H (z - G z) = 0}`. -/

namespace IntLInfty.Kan.A83H

open IntLInfty.Kan IntLInfty.Kan.A83 IntLInfty.Kan.A83Cone IntLInfty.Kan.A83Poinc
  IntLInfty.Kan.A83Fill IntLInfty.Kan.A83Proj IntLInfty.Kan.A83KK IntLInfty.Kan.A83KL
  IntLInfty.Kan.A83Ev IntLInfty.Kan.A83IntegK IntLInfty.Kan.A83G
  IntLInfty.Kan.A83Graph
open scoped ContDiff


variable {m r : ℕ} {L : ℕ → Type} [∀ i, AddCommGroup (L i)] [∀ i, Module ℝ (L i)]
  [∀ i, FiniteDimensional ℝ (L i)]

end IntLInfty.Kan.A83H

/-! ### K0b-iii (Relay 25): weighted jet norms for the Volterra estimate `hV`.
Plan: an equivalent weighted norm `‖(W v.1, η W v.2)‖` on `Amb` with
`W w I k β y = ε^k e^{-λ‖y‖} w I k β y`; the cone operator gains `1/λ + ε` in it, pointwise
(local) operators are bounded uniformly in `λ, ε`, hence `fderiv Gmap` is a contraction for it. -/

namespace IntLInfty.Kan.A83W

open IntLInfty.Kan
open scoped BoundedContinuousFunction

variable {r m : ℕ}

end IntLInfty.Kan.A83W

/-! (D) Weighted bounds for the cone integral and the cone operator `K`:
`e^{-λ‖y‖} ‖D^j (coneInt p f) y‖ ≤ M` and `‖y‖ e^{-λ‖y‖} ‖D^j (coneInt p f) y‖ ≤ M/λ` when
`e^{-λ‖z‖} ‖D^j f z‖ ≤ M` on the star-shaped set. -/

namespace IntLInfty.Kan.A83W

open IntLInfty.Kan IntLInfty.Kan.A83 IntLInfty.Kan.A83Cone IntLInfty.Kan.A83Poinc Set

section ConeW

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {S : Set E}

end ConeW


variable {m : ℕ}

end IntLInfty.Kan.A83W

/-! ### K0b-iii (Relay 26) (E): jet components vs `‖D^k f(y)‖` (pointwise norm equivalence). -/

namespace IntLInfty.Kan.A83E

open IntLInfty.Kan IntLInfty.Kan.A83

variable {m k : ℕ}

variable {r : ℕ} {f : (Fin m → ℝ) → ℝ}

open IntLInfty.Kan.A83Poinc


variable {ω : Ω m}

end IntLInfty.Kan.A83E

/-! ### K0b-iii (Relay 26) (F): weighted Leibniz bound for the wedge product. -/

namespace IntLInfty.Kan.A83E

open IntLInfty.Kan IntLInfty.Kan.A83 IntLInfty.Kan.A83Poinc IntLInfty.Kan.A83Leib


variable {m r k : ℕ}

end IntLInfty.Kan.A83E

/-! Relay 27 (G1/G2): weighted bounds for the wedge product on jets. `K = ‖mulB m‖ (2m+1)^r`.
Weight on one factor: `‖W (γη)‖ ≤ K ‖W γ‖ ‖η‖` (value parts), and the `d`-part via `extD_mul`. -/
namespace IntLInfty.Kan.A83G1

open IntLInfty.Kan IntLInfty.Kan.A83 IntLInfty.Kan.A83Poinc IntLInfty.Kan.A83Leib
  IntLInfty.Kan.A83Wedge IntLInfty.Kan.A83W IntLInfty.Kan.A83E


variable {m r : ℕ}

end IntLInfty.Kan.A83G1

/-! Relay 27 (G3, part 1): locality of the derivative of smooth jet families. `Loc Q1 Q2 a` says
`‖W (Da(x) v).val‖ ≤ C Q1(v)` and `‖W (Da(x) v).d‖ ≤ C (Q1(v) + Q2(v))` with `C` independent of the
weights `λ, ε`; it is threaded through the `SmoothFam` combinators (zero, const, add, smul, sum,
wedge, congr, continuous linear maps). -/
namespace IntLInfty.Kan.A83Loc

open IntLInfty.Kan IntLInfty.Kan.A83 IntLInfty.Kan.A83Poinc IntLInfty.Kan.A83Leib
  IntLInfty.Kan.A83Wedge IntLInfty.Kan.A83W IntLInfty.Kan.A83Ev IntLInfty.Kan.A83G1
  IntLInfty.Kan.A83Proj
open scoped ContDiff


variable {m r : ℕ}

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

variable {Q1 Q2 : ℝ → ℝ → E → ℝ}

end IntLInfty.Kan.A83Loc

/-! Relay 27 (G3, part 2): locality through sums of homogeneous families, `ceLift`, the generator
values on `Amb`, and the defect family `Gfam`. -/
namespace IntLInfty.Kan.A83Loc

open IntLInfty.Kan IntLInfty.Kan.A83 IntLInfty.Kan.A83Leib IntLInfty.Kan.A83DGA
  IntLInfty.Kan.A83Wedge IntLInfty.Kan.A83Proj IntLInfty.Kan.A83W IntLInfty.Kan.A83Ev
  IntLInfty.Kan.A83G IntLInfty.Kan.A83IntegK
open scoped ContDiff

section Sum

variable {m r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {Q1 Q2 : ℝ → ℝ → E → ℝ}

variable {L : ℕ → Type} [∀ i, AddCommGroup (L i)] [∀ i, Module ℝ (L i)]

end Sum

section AmbLoc

variable {m r : ℕ} {L : ℕ → Type} [∀ i, AddCommGroup (L i)] [∀ i, Module ℝ (L i)]
  [∀ i, FiniteDimensional ℝ (L i)]

end AmbLoc

end IntLInfty.Kan.A83Loc

/-! ### K0b-iii (H1, H2): `fderiv Gmap` coordinatewise, and weighted bounds for `K`. -/

namespace IntLInfty.Kan.A83H2

open IntLInfty.Kan IntLInfty.Kan.A83 IntLInfty.Kan.A83Cone IntLInfty.Kan.A83Poinc
  IntLInfty.Kan.A83Proj IntLInfty.Kan.A83KK IntLInfty.Kan.A83KL IntLInfty.Kan.A83Ev
  IntLInfty.Kan.A83IntegK IntLInfty.Kan.A83G IntLInfty.Kan.A83H IntLInfty.Kan.A83W
  IntLInfty.Kan.A83E IntLInfty.Kan.A83G1 IntLInfty.Kan.A83Loc
open scoped ContDiff


variable {m r : ℕ}

section AmbH

variable {L : ℕ → Type} [∀ i, AddCommGroup (L i)] [∀ i, Module ℝ (L i)]
  [∀ i, FiniteDimensional ℝ (L i)]

end AmbH

end IntLInfty.Kan.A83H2

/-! ### K0b-iii (H3): the Volterra bound `hV`, hence `∫_S` is a split submanifold. -/

namespace IntLInfty.Kan.A83H3

open IntLInfty.Kan IntLInfty.Kan.A83 IntLInfty.Kan.A83Poinc
  IntLInfty.Kan.A83KL IntLInfty.Kan.A83Ev
  IntLInfty.Kan.A83IntegK IntLInfty.Kan.A83G IntLInfty.Kan.A83H IntLInfty.Kan.A83W
  IntLInfty.Kan.A83G1 IntLInfty.Kan.A83Loc IntLInfty.Kan.A83H2
open scoped ContDiff


variable {m r : ℕ} {L : ℕ → Type} [∀ i, AddCommGroup (L i)] [∀ i, Module ℝ (L i)]
  [∀ i, FiniteDimensional ℝ (L i)]

end IntLInfty.Kan.A83H3

/-! R29 (RelHorn route): the fixed-point set of a `C^∞` idempotent self-map of a Banach space
is a split submanifold. Used with `R = kanMap ∘ retraction ∘ filler` to get `RelHorn` split. -/
namespace IntLInfty.Kan.A83Fix

open IntLInfty.Kan Filter Topology
open scoped ContDiff

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

end IntLInfty.Kan.A83Fix

/-! R29 (RelHorn route, part 2): local versions. A set is a split submanifold iff it is locally
a `C^∞` retract (only the two directions needed below). -/
namespace IntLInfty.Kan.A83Fix

open IntLInfty.Kan Filter Topology
open scoped ContDiff

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

end IntLInfty.Kan.A83Fix

/-! R29 (RelHorn route, part 3): the target of a smooth map with global smooth fillers out of a
split submanifold is a split submanifold. Instance: `RelHorn` = target of `kanMap`. -/
namespace IntLInfty.Kan.A83Fix

open IntLInfty.Kan Filter Topology
open scoped ContDiff

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {G : Type} [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]

end IntLInfty.Kan.A83Fix

/-! R29: assembly of `IsKanFibration` from global smooth fillers of `kanMap` (RelHorn split via
`A83Fix.isSplitSubmanifold_of_filler`, surjective submersion via `A83Graph.isSurjSubmersionOn_of_filler`). -/
namespace IntLInfty.Kan.A83Kan

open IntLInfty.Kan
open scoped ContDiff

variable {L : ℕ → Type} [∀ i, AddCommGroup (L i)] [∀ i, Module ℝ (L i)]
  [∀ i, FiniteDimensional ℝ (L i)]

end IntLInfty.Kan.A83Kan

/-! R30: inputs (1)-(3) of `A83Kan.isKanFibration_of_filler`: `kanMap` is a continuous linear map
(hence `C^∞`), it maps `∫_S` into `RelHorn`, and `0 ∈ ∫_S` (augmentation `CE L → ℝ`). -/
namespace IntLInfty.Kan.A83KM

open IntLInfty.Kan IntLInfty.Kan.A83
open scoped ContDiff

variable {L : ℕ → Type} [∀ i, AddCommGroup (L i)] [∀ i, Module ℝ (L i)]
  [∀ i, FiniteDimensional ℝ (L i)]

theorem hornCompat_faceAmb {r : ℕ} (hr : 1 ≤ r) (S : GenSys L) (m : ℕ) (j : Fin (m + 2))
    (z : Amb r S (m + 1)) :
    HornCompat (fun q => faceAmb r S q) m j (fun i => faceAmb r S m i.1 z) := by
  cases m with
  | zero => trivial
  | succ q =>
    intro a b hab ha hb
    funext t k
    exact faceCr_faceCr hr hab (z (Fin.castSucc (Fin.castSucc t)) k)

theorem jet_zero'' {r m : ℕ} (hr : 1 ≤ r) : jet r (0 : Ω m) = 0 := by
  have := jet_smul hr (0 : ℝ) (isCr_zero (r := r) (m := m))
  simpa using this

end IntLInfty.Kan.A83KM

/-! R30: `isKanFibration_of_filler` with inputs (1)-(3) discharged: only the fillers remain. -/
namespace IntLInfty.Kan.A83Kan

open IntLInfty.Kan
open scoped ContDiff

variable {L : ℕ → Type} [∀ i, AddCommGroup (L i)] [∀ i, Module ℝ (L i)]
  [∀ i, FiniteDimensional ℝ (L i)]

end IntLInfty.Kan.A83Kan

/-! R31: filler data at one level, composition of fillers along `S'' ≤ S' ≤ S` (the tower step of
K3), and the Kan-fibration assembly from level-wise fillers (different towers per level). -/
namespace IntLInfty.Kan.A83Comp

open IntLInfty.Kan IntLInfty.Kan.A83
open scoped ContDiff

variable {L : ℕ → Type} [∀ i, AddCommGroup (L i)] [∀ i, Module ℝ (L i)]
  [∀ i, FiniteDimensional ℝ (L i)]

end IntLInfty.Kan.A83Comp

/-! R32: K2 algebra. `D = ∂*ₙ : L*ₙ → L*ₙ₊₁` with `δ(genₙ b) - genₙ₊₁(D b) ∈ lowAlg n`, a section
`secD` of `D` on its range, `kerSub n = ker D`, `imSub (n+1) = range D`, and the generator-level DGA
lemma for `tauLt (n+1)`: the `tauLe n` conditions plus the forced degree-`n+1` values give the
condition for every generator of `tauLt (n+1)`. -/
namespace IntLInfty.Kan.A83K2

open IntLInfty.Kan IntLInfty.Kan.A83

variable {L : ℕ → Type} [∀ i, AddCommGroup (L i)] [∀ i, Module ℝ (L i)]

end IntLInfty.Kan.A83K2

/-! R33: CrForms-valued generator values on the ambient space (K2 filler step 1). -/
namespace IntLInfty.Kan.A83K2V

open IntLInfty.Kan IntLInfty.Kan.A83
open scoped ContDiff

variable {L : ℕ → Type} [∀ i, AddCommGroup (L i)] [∀ i, Module ℝ (L i)]
  [∀ i, FiniteDimensional ℝ (L i)]

/-- `CrForms`-valued generator values of `w : Amb r S m` (degree `≥ m` generators go to `0`). -/
noncomputable def valC {r m : ℕ} (S : GenSys L) (w : Amb r S m) (t : ℕ) :
    Module.Dual ℝ (L t) →ₗ[ℝ] CrForms r m (t + 1) :=
  if h : t < m then
    ∑ k : Fin (Module.finrank ℝ (S t)), LinearMap.smulRight
      ((Finsupp.lapply k).comp ((genBasis S t).repr.toLinearMap.comp (A83Ev.retr S t)))
      (w ⟨t, h⟩ k)
  else 0

theorem valC_lt {r m : ℕ} (S : GenSys L) (w : Amb r S m) {t : ℕ} (h : t < m)
    (ξ : Module.Dual ℝ (L t)) :
    valC S w t ξ = ∑ k : Fin (Module.finrank ℝ (S t)),
      (genBasis S t).repr (A83Ev.retr S t ξ) k • w ⟨t, h⟩ k := by
  simp only [valC, h, ↓reduceDIte, LinearMap.sum_apply,
    LinearMap.smulRight_apply, LinearMap.comp_apply, Finsupp.lapply_apply,
    LinearEquiv.coe_coe]

theorem valC_ge {r m : ℕ} (S : GenSys L) (w : Amb r S m) {t : ℕ} (h : ¬ t < m)
    (ξ : Module.Dual ℝ (L t)) : valC S w t ξ = 0 := by
  simp only [valC, h, ↓reduceDIte, LinearMap.zero_apply]

theorem valC_of_mem {r m : ℕ} (S : GenSys L) (w : Amb r S m) {t : ℕ} (h : t < m)
    {ξ : Module.Dual ℝ (L t)} (hξ : ξ ∈ S t) :
    valC S w t ξ = ∑ k : Fin (Module.finrank ℝ (S t)),
      (genBasis S t).repr ⟨ξ, hξ⟩ k • w ⟨t, h⟩ k := by
  have e : A83Ev.retr S t ξ = ⟨ξ, hξ⟩ := A83Ev.retr_spec S t ⟨ξ, hξ⟩
  rw [valC_lt S w h, e]

theorem valC_basis {r m : ℕ} (S : GenSys L) (w : Amb r S m) (t : Fin m)
    (k : Fin (Module.finrank ℝ (S t))) :
    valC S w t (genBasis S t k : Module.Dual ℝ (L t)) = w t k := by
  rw [valC_of_mem S w t.2 (genBasis S t k).2, Module.Basis.repr_self]
  simp only [Finsupp.single_apply, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq,
    Finset.mem_univ, ↓reduceIte, Fin.eta]

theorem valC_add {r m : ℕ} (S : GenSys L) (w w' : Amb r S m) (t : ℕ)
    (ξ : Module.Dual ℝ (L t)) : valC S (w + w') t ξ = valC S w t ξ + valC S w' t ξ := by
  by_cases h : t < m
  · rw [valC_lt S _ h, valC_lt S _ h, valC_lt S _ h, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ => smul_add _ _ _
  · rw [valC_ge S _ h, valC_ge S _ h, valC_ge S _ h, add_zero]

theorem valC_smul {r m : ℕ} (S : GenSys L) (c : ℝ) (w : Amb r S m) (t : ℕ)
    (ξ : Module.Dual ℝ (L t)) : valC S (c • w) t ξ = c • valC S w t ξ := by
  by_cases h : t < m
  · rw [valC_lt S _ h, valC_lt S _ h, Finset.smul_sum]
    exact Finset.sum_congr rfl fun k _ => smul_comm (_ : ℝ) c (w ⟨t, h⟩ k)
  · rw [valC_ge S _ h, valC_ge S _ h, smul_zero]

theorem continuous_valC {r m : ℕ} (S : GenSys L) (t : ℕ) (ξ : Module.Dual ℝ (L t)) :
    Continuous fun w : Amb r S m => valC S w t ξ := by
  by_cases h : t < m
  · simp only [valC_lt S _ h]
    exact continuous_finset_sum _ fun k _ =>
      (continuous_const_smul _).comp ((continuous_apply k).comp (continuous_apply (⟨t, h⟩ : Fin m)))
  · simp only [valC_ge S _ h]
    exact continuous_const

/-- `w ↦ valC S w t ξ` as a continuous linear map. -/
noncomputable def valCLM {r : ℕ} (S : GenSys L) (m t : ℕ) (ξ : Module.Dual ℝ (L t)) :
    Amb r S m →L[ℝ] CrForms r m (t + 1) where
  toFun w := valC S w t ξ
  map_add' w w' := valC_add S w w' t ξ
  map_smul' c w := valC_smul S c w t ξ
  cont := continuous_valC S t ξ

/-- Restriction `S' ≤ S` does not change the values on `S'`. -/
theorem valC_res {r m : ℕ} {S S' : GenSys L} (hS : ∀ i, S' i ≤ S i) (w : Amb r S m) (t : ℕ)
    {ξ : Module.Dual ℝ (L t)} (hξ : ξ ∈ S' t) : valC S' (res hS w) t ξ = valC S w t ξ := by
  by_cases h : t < m
  · have e1 : (⟨ξ, hS t hξ⟩ : S t) = Submodule.inclusion (hS t) ⟨ξ, hξ⟩ := rfl
    rw [valC_of_mem S' (res hS w) h hξ, valC_of_mem S w h (hS t hξ), e1]
    conv_rhs => rw [← (genBasis S' t).sum_repr ⟨ξ, hξ⟩]
    simp only [res, map_sum, map_smul, Finsupp.coe_finset_sum, Finsupp.coe_smul,
      Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.smul_sum, Finset.sum_smul, mul_smul]
    exact Finset.sum_comm
  · rw [valC_ge S' _ h, valC_ge S _ h]

/-- Faces commute with the values (for `t < m`). -/
theorem valC_face {r m : ℕ} (hr : 1 ≤ r) (S : GenSys L) (i : Fin (m + 2)) (w : Amb r S (m + 1))
    {t : ℕ} (h : t < m) (ξ : Module.Dual ℝ (L t)) :
    valC S (faceAmb r S m i w) t ξ = faceLin (r := r) (m := m) hr (t + 1) i (valC S w t ξ) := by
  rw [valC_lt S _ h, valC_lt S _ (Nat.lt_succ_of_lt h), map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_smul]
  rfl

/-- No `n`-forms on `Δᵐ` for `n > m`. -/
theorem crForms_eq_zero_of_lt {r m n : ℕ} (hr : 1 ≤ r) (h : m < n) (w : CrForms r m n) : w = 0 := by
  have hs := A83Wedge.wRep_spec hr w
  have e : FormEqOn (A83Wedge.wRep hr w) 0 := fun x hx =>
    A83Defect.extPow_eq_zero_of_lt
      (by simp only [Subspace.dual_finrank_eq, Module.finrank_fin_fun]; exact h) (hs.1.1 x hx)
  apply Subtype.ext
  rw [← hs.2, jet_congr e, A83KM.jet_zero'' hr]
  rfl

/-- Compatible ambient horns give compatible `CrForms` horns of values. -/
theorem hornCompat_valC {r m : ℕ} (hr : 1 ≤ r) (S : GenSys L) (j : Fin (m + 2))
    (p : {i : Fin (m + 2) // i ≠ j} → Amb r S m)
    (hp : HornCompat (fun q => faceAmb r S q) m j p) (t : ℕ) (ξ : Module.Dual ℝ (L t)) :
    HornCompat (X := fun q => ↥(CrForms r q (t + 1))) (fun q => faceCr r q (t + 1)) m j
      (fun i => valC S (p i) t ξ) := by
  cases m with
  | zero => trivial
  | succ q =>
    intro a b hab ha hb
    by_cases ht : t < q
    · have e := congrArg (fun w => valC S w t ξ) (hp a b hab ha hb)
      simp only at e
      rw [valC_face hr S a _ ht, valC_face hr S b _ ht] at e
      exact e
    · exact (crForms_eq_zero_of_lt hr (by omega) _).trans (crForms_eq_zero_of_lt hr (by omega) _).symm

theorem hornCompat_sub_cr {r m n : ℕ} (hr : 1 ≤ r) (j : Fin (m + 2))
    (u v : {i : Fin (m + 2) // i ≠ j} → CrForms r m n)
    (hu : HornCompat (X := fun q => ↥(CrForms r q n)) (fun q => faceCr r q n) m j u)
    (hv : HornCompat (X := fun q => ↥(CrForms r q n)) (fun q => faceCr r q n) m j v) :
    HornCompat (X := fun q => ↥(CrForms r q n)) (fun q => faceCr r q n) m j (u - v) := by
  cases m with
  | zero => trivial
  | succ q =>
    intro a b hab ha hb
    have e1 := hu a b hab ha hb
    have e2 := hv a b hab ha hb
    show faceLin (r := r) (m := q) hr n a (u _ - v _) = faceLin (r := r) (m := q) hr n b (u _ - v _)
    rw [map_sub, map_sub]
    exact congrArg₂ (· - ·) e1 e2

/-- The projection onto `S' t` (a chosen retraction). -/
noncomputable def projS (S' : GenSys L) (t : ℕ) : Module.Dual ℝ (L t) →ₗ[ℝ] Module.Dual ℝ (L t) :=
  (S' t).subtype ∘ₗ A83Ev.retr S' t

theorem projS_mem (S' : GenSys L) (t : ℕ) (ξ : Module.Dual ℝ (L t)) : projS S' t ξ ∈ S' t :=
  (A83Ev.retr S' t ξ).2

theorem projS_of_mem (S' : GenSys L) (t : ℕ) {ξ : Module.Dual ℝ (L t)} (h : ξ ∈ S' t) :
    projS S' t ξ = ξ := by
  show ((A83Ev.retr S' t ξ : S' t) : Module.Dual ℝ (L t)) = ξ
  have e : A83Ev.retr S' t ξ = ⟨ξ, h⟩ := A83Ev.retr_spec S' t ⟨ξ, h⟩
  rw [e]

/-- The point of the ambient space with prescribed generator values. -/
noncomputable def mkAmb {r m : ℕ} (S : GenSys L)
    (F : ∀ t : ℕ, Module.Dual ℝ (L t) →ₗ[ℝ] CrForms r m (t + 1)) : Amb r S m :=
  fun t k => F t (genBasis S t k)

theorem valC_mkAmb {r m : ℕ} (S : GenSys L)
    (F : ∀ t : ℕ, Module.Dual ℝ (L t) →ₗ[ℝ] CrForms r m (t + 1)) {t : ℕ} (h : t < m)
    {ξ : Module.Dual ℝ (L t)} (hξ : ξ ∈ S t) : valC S (mkAmb S F) t ξ = F t ξ := by
  have e : ξ = ∑ k, (genBasis S t).repr ⟨ξ, hξ⟩ k •
      ((genBasis S t k : S t) : Module.Dual ℝ (L t)) := by
    have h1 := congrArg Subtype.val ((genBasis S t).sum_repr ⟨ξ, hξ⟩)
    rw [Submodule.coe_sum] at h1
    exact h1.symm
  rw [valC_of_mem S _ h hξ]
  conv_rhs => rw [e]
  rw [map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_smul]
  rfl

/-- The horn correction: fill the defect `p - (faces of x)` with the linear horn section. -/
noncomputable def corrL {r m : ℕ} (hr : 1 ≤ r) (S : GenSys L) (j : Fin (m + 2))
    (x : Amb r S (m + 1)) (p : {i : Fin (m + 2) // i ≠ j} → Amb r S m) (t : ℕ) :
    Module.Dual ℝ (L t) →ₗ[ℝ] CrForms r (m + 1) (t + 1) :=
  (secCLM (m := m) hr (t + 1) j).toLinearMap ∘ₗ
    LinearMap.pi fun l => valC S (p l) t - valC S (faceAmb r S m l.1 x) t

theorem corrL_apply {r m : ℕ} (hr : 1 ≤ r) (S : GenSys L) (j : Fin (m + 2))
    (x : Amb r S (m + 1)) (p : {i : Fin (m + 2) // i ≠ j} → Amb r S m) (t : ℕ)
    (ζ : Module.Dual ℝ (L t)) :
    corrL hr S j x p t ζ = secCLM (m := m) hr (t + 1) j
      (fun l => valC S (p l) t ζ - valC S (faceAmb r S m l.1 x) t ζ) := rfl

/-- Generator values of the filler: `S'`-part from `y.2`, complement from `x` plus horn correction. -/
noncomputable def fillL {r m : ℕ} (hr : 1 ≤ r) {S S' : GenSys L} (j : Fin (m + 2))
    (x : Amb r S (m + 1)) (y : ({i : Fin (m + 2) // i ≠ j} → Amb r S m) × Amb r S' (m + 1))
    (t : ℕ) : Module.Dual ℝ (L t) →ₗ[ℝ] CrForms r (m + 1) (t + 1) :=
  valC S' y.2 t ∘ₗ projS S' t + (valC S x t + corrL hr S j x y.1 t) ∘ₗ (LinearMap.id - projS S' t)

theorem fillL_apply {r m : ℕ} (hr : 1 ≤ r) {S S' : GenSys L} (j : Fin (m + 2))
    (x : Amb r S (m + 1)) (y : ({i : Fin (m + 2) // i ≠ j} → Amb r S m) × Amb r S' (m + 1))
    (t : ℕ) (ξ : Module.Dual ℝ (L t)) :
    fillL hr j x y t ξ = valC S' y.2 t (projS S' t ξ) +
      (valC S x t (ξ - projS S' t ξ) + corrL hr S j x y.1 t (ξ - projS S' t ξ)) := rfl

noncomputable def fillZ {r m : ℕ} (hr : 1 ≤ r) {S S' : GenSys L} (j : Fin (m + 2))
    (x : Amb r S (m + 1)) (y : ({i : Fin (m + 2) // i ≠ j} → Amb r S m) × Amb r S' (m + 1)) :
    Amb r S (m + 1) :=
  mkAmb S fun t => fillL hr j x y t

theorem valC_fillZ {r m : ℕ} (hr : 1 ≤ r) {S S' : GenSys L} (j : Fin (m + 2))
    (x : Amb r S (m + 1)) (y : ({i : Fin (m + 2) // i ≠ j} → Amb r S m) × Amb r S' (m + 1))
    {t : ℕ} (ht : t < m + 1) {ξ : Module.Dual ℝ (L t)} (hξ : ξ ∈ S t) :
    valC S (fillZ hr j x y) t ξ = fillL hr j x y t ξ :=
  valC_mkAmb S _ ht hξ

/-- (P1) the filler restricts to `y.2`. -/
theorem res_fillZ {r m : ℕ} (hr : 1 ≤ r) {S S' : GenSys L} (h : ∀ i, S' i ≤ S i) (j : Fin (m + 2))
    (x : Amb r S (m + 1)) (y : ({i : Fin (m + 2) // i ≠ j} → Amb r S m) × Amb r S' (m + 1)) :
    res h (fillZ hr j x y) = y.2 := by
  funext t k
  have hb := (genBasis S' t k).2
  rw [← valC_basis S' (res h (fillZ hr j x y)) t k, valC_res h (fillZ hr j x y) (t : ℕ) hb,
    valC_fillZ hr j x y t.2 (h t hb), fillL_apply, projS_of_mem S' _ hb, sub_self, map_zero,
    map_zero, add_zero, add_zero, valC_basis]

/-- (P2) generator level: the faces `i ≠ j` of the filler values are the horn values. -/
theorem face_fillL {r m : ℕ} (hr : 1 ≤ r) {S S' : GenSys L} (h : ∀ i, S' i ≤ S i)
    (j : Fin (m + 2)) (x : Amb r S (m + 1))
    (y : ({i : Fin (m + 2) // i ≠ j} → Amb r S m) × Amb r S' (m + 1))
    (hp : HornCompat (fun q => faceAmb r S q) m j y.1)
    (hy : ∀ i, faceAmb r S' m i.1 y.2 = res h (y.1 i))
    (i : {i : Fin (m + 2) // i ≠ j}) {t : ℕ} (ht : t < m) (ξ : Module.Dual ℝ (L t)) :
    faceLin (r := r) (m := m) hr (t + 1) i.1 (fillL hr j x y t ξ) = valC S (y.1 i) t ξ := by
  rw [fillL_apply, map_add, map_add, corrL_apply, ← valC_face hr S' i.1 y.2 ht (projS S' t ξ),
    hy i, valC_res h _ t (projS_mem S' t ξ), ← valC_face hr S i.1 x ht (ξ - projS S' t ξ)]
  have hc : HornCompat (X := fun q => ↥(CrForms r q (t + 1))) (fun q => faceCr r q (t + 1)) m j
      (fun l => valC S (y.1 l) t (ξ - projS S' t ξ) -
        valC S (faceAmb r S m l.1 x) t (ξ - projS S' t ξ)) :=
    hornCompat_sub_cr hr j _ _ (hornCompat_valC hr S j y.1 hp t _)
      (hornCompat_valC hr S j _ (A83KM.hornCompat_faceAmb hr S m j x) t _)
  have hs : faceLin (r := r) (m := m) hr (t + 1) i.1 (secCLM (m := m) hr (t + 1) j
      (fun l => valC S (y.1 l) t (ξ - projS S' t ξ) -
        valC S (faceAmb r S m l.1 x) t (ξ - projS S' t ξ))) =
      valC S (y.1 i) t (ξ - projS S' t ξ) - valC S (faceAmb r S m i.1 x) t (ξ - projS S' t ξ) :=
    congrFun (secLin_spec hr j _ hc) i
  rw [hs, add_sub_cancel, ← map_add, add_sub_cancel]

/-- (P2) the faces `i ≠ j` of the filler are the horn. -/
theorem face_fillZ {r m : ℕ} (hr : 1 ≤ r) {S S' : GenSys L} (h : ∀ i, S' i ≤ S i)
    (j : Fin (m + 2)) (x : Amb r S (m + 1))
    (y : ({i : Fin (m + 2) // i ≠ j} → Amb r S m) × Amb r S' (m + 1))
    (hp : HornCompat (fun q => faceAmb r S q) m j y.1)
    (hy : ∀ i, faceAmb r S' m i.1 y.2 = res h (y.1 i)) (i : {i : Fin (m + 2) // i ≠ j}) :
    faceAmb r S m i.1 (fillZ hr j x y) = y.1 i := by
  funext t k
  rw [← valC_basis S (faceAmb r S m i.1 (fillZ hr j x y)) t k, valC_face hr S i.1 _ t.2,
    valC_fillZ hr j x y (Nat.lt_succ_of_lt t.2) (genBasis S t k).2,
    face_fillL hr h j x y hp hy i t.2, valC_basis]

theorem fillL_kan {r m : ℕ} (hr : 1 ≤ r) {S S' : GenSys L} (h : ∀ i, S' i ≤ S i)
    (j : Fin (m + 2)) (x : Amb r S (m + 1)) (t : ℕ) (ξ : Module.Dual ℝ (L t)) :
    fillL hr j x (kanMap h m j x) t ξ = valC S x t ξ := by
  have e0 : (fun l : {i : Fin (m + 2) // i ≠ j} =>
      valC S ((kanMap h m j x).1 l) t (ξ - projS S' t ξ) -
        valC S (faceAmb r S m l.1 x) t (ξ - projS S' t ξ)) = 0 := funext fun l => sub_self _
  rw [fillL_apply, corrL_apply, e0, map_zero, add_zero]
  show valC S' (res h x) t (projS S' t ξ) + valC S x t (ξ - projS S' t ξ) = _
  rw [valC_res h x t (projS_mem S' t ξ), ← map_add, add_sub_cancel]

/-- (P3) the filler fixes `x` on `kanMap x`. -/
theorem fillZ_kan {r m : ℕ} (hr : 1 ≤ r) {S S' : GenSys L} (h : ∀ i, S' i ≤ S i)
    (j : Fin (m + 2)) (x : Amb r S (m + 1)) : fillZ hr j x (kanMap h m j x) = x := by
  funext t k
  show fillL hr j x (kanMap h m j x) t (genBasis S t k) = x t k
  rw [fillL_kan hr h j x, valC_basis]

/-- (P4) the filler is `C^∞` (affine) in the horn data. -/
theorem contDiff_fillZ {r m : ℕ} (hr : 1 ≤ r) {S S' : GenSys L} (j : Fin (m + 2))
    (x : Amb r S (m + 1)) :
    ContDiff ℝ ∞ (fun y : ({i : Fin (m + 2) // i ≠ j} → Amb r S m) × Amb r S' (m + 1) =>
      fillZ hr j x y) := by
  have key : ∀ (t : Fin (m + 1)) (k : Fin (Module.finrank ℝ (S t))),
      ContDiff ℝ ∞ (fun y : ({i : Fin (m + 2) // i ≠ j} → Amb r S m) × Amb r S' (m + 1) =>
        fillL hr j x y t (genBasis S t k)) := by
    intro t k
    simp only [fillL_apply, corrL_apply]
    exact ((valCLM S' (m + 1) t _).contDiff.comp contDiff_snd).add (contDiff_const.add
      ((secCLM (m := m) hr ((t : ℕ) + 1) j).contDiff.comp (contDiff_pi.2 fun l =>
        ((valCLM S m t _).contDiff.comp (contDiff_pi.1 contDiff_fst l)).sub contDiff_const)))
  exact contDiff_pi.2 fun t => contDiff_pi.2 fun k => key t k

end IntLInfty.Kan.A83K2V

namespace IntLInfty.Kan.A83K1c

open IntLInfty.Kan IntLInfty.Kan.A83 IntLInfty.Kan.A83KM IntLInfty.Kan.A83K2V
open scoped ContDiff

variable {L : ℕ → Type} [∀ i, AddCommGroup (L i)] [∀ i, Module ℝ (L i)]
  [∀ i, FiniteDimensional ℝ (L i)]

theorem res_mkAmb_eq {r m : ℕ} {S S' : GenSys L} (h : ∀ i, S' i ≤ S i)
    (F : ∀ t : ℕ, Module.Dual ℝ (L t) →ₗ[ℝ] CrForms r m (t + 1)) :
    res h (mkAmb S F) = mkAmb S' F := by
  funext t k
  have e : ∑ l, (genBasis S t).repr (Submodule.inclusion (h t) (genBasis S' t k)) l •
      ((genBasis S t l : S t) : Module.Dual ℝ (L t)) = (genBasis S' t k : Module.Dual ℝ (L t)) := by
    have h1 := congrArg Subtype.val
      ((genBasis S t).sum_repr (Submodule.inclusion (h t) (genBasis S' t k)))
    rw [Submodule.coe_sum] at h1
    simpa only [Submodule.coe_smul, Submodule.coe_inclusion] using h1
  simp only [res, mkAmb]
  conv_rhs => rw [← e]
  rw [map_sum]
  simp only [map_smul]

theorem mkAmb_valC_self {r m : ℕ} (S : GenSys L) (w : Amb r S m) : mkAmb S (valC S w) = w := by
  funext t k
  show valC S w t (genBasis S t k) = w t k
  rw [valC_of_mem S w t.isLt (genBasis S t k).2]
  simp [Module.Basis.repr_self, Finsupp.single_apply]

/-- A continuous linear section of `res`. -/
noncomputable def secCLM (S S' : GenSys L) (r m : ℕ) : Amb r S' m →L[ℝ] Amb r S m :=
  ContinuousLinearMap.pi fun t => ContinuousLinearMap.pi fun k => valCLM S' m t (genBasis S t k)

theorem secCLM_eq {r m : ℕ} (S S' : GenSys L) (y : Amb r S' m) :
    secCLM S S' r m y = mkAmb S (valC S' y) := rfl

theorem res_secCLM {r m : ℕ} {S S' : GenSys L} (h : ∀ i, S' i ≤ S i) (y : Amb r S' m) :
    res h (secCLM S S' r m y) = y := by
  rw [secCLM_eq, res_mkAmb_eq, mkAmb_valC_self]

end IntLInfty.Kan.A83K1c

open scoped ContDiff

open IntLInfty.Kan in
theorem solution (r : ℕ) (hr : 1 ≤ r) (L : ℕ → Type) [∀ i, AddCommGroup (L i)]
    [∀ i, Module ℝ (L i)] [∀ i, FiniteDimensional ℝ (L i)] (S S' : GenSys L)
    (h : ∀ i, S' i ≤ S i) :
    (∀ (m : ℕ) (j : Fin (m + 2)),
      ∃ Z : Amb r S (m + 1) → (({i : Fin (m + 2) // i ≠ j} → Amb r S m) × Amb r S' (m + 1)) →
          Amb r S (m + 1),
        (∀ x, ContDiff ℝ ∞ (Z x)) ∧
        (∀ x y, res h (Z x y) = y.2) ∧
        (∀ x (y : ({i : Fin (m + 2) // i ≠ j} → Amb r S m) × Amb r S' (m + 1)),
          HornCompat (fun q => faceAmb r S q) m j y.1 →
          (∀ i, faceAmb r S' m i.1 y.2 = res h (y.1 i)) → ∀ i, faceAmb r S m i.1 (Z x y) = y.1 i) ∧
        (∀ x, Z x (kanMap h m j x) = x)) ∧
    (∀ m, ∃ s : Amb r S' m →L[ℝ] Amb r S m, ∀ y, res h (s y) = y) := by
  exact
      ⟨fun _ j => ⟨fun x y => A83K2V.fillZ hr j x y, fun x => A83K2V.contDiff_fillZ hr j x,
         fun x y => A83K2V.res_fillZ hr h j x y,
         fun x y hp hy i => A83K2V.face_fillZ hr h j x y hp hy i,
         fun x => A83K2V.fillZ_kan hr h j x⟩,
       fun m => ⟨A83K1c.secCLM S S' r m, fun y => A83K1c.res_secCLM h y⟩⟩
