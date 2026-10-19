-- Prove2me | solution 1 for OAI.ThresholdParallelRepetition.MixedExposure.EventSystem.rawA_norm
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T23:56:39.998909+00:00
-- url     : https://prove2.me/submissions/6a22b392-b8a9-4d23-b0aa-a476e888f0eb

import Mathlib
import Definitions.Def_EntangledGames
import Definitions.Def_OAI_Probability_EntangledGames_Basic
import Definitions.Def_OAI_Probability_EntangledGames_Resolvent
import Definitions.Def_OAI_Probability_EntangledGames_SpectralEntropy
import Definitions.Def_OAI_Probability_EntangledGames_Purification
import Definitions.Def_OAI_Probability_EntangledGames_MeasurementTransport
import Definitions.Def_OAI_Probability_EntangledGames_HilbertSchmidt
import Definitions.Def_OAI_Probability_EntangledGames_SpectralBins
import Definitions.Def_OAI_Probability_EntangledGames_CoherentFilters
import Definitions.Def_OAI_Probability_EntangledGames_SamplingStrategy
import Definitions.Def_OAI_Probability_EntangledGames_CorrelatedSampling
import Definitions.Def_OAI_Probability_EntangledGames_FiniteProbability
import Definitions.Def_OAI_Probability_EntangledGames_RelativeEntropy
import Definitions.Def_OAI_Probability_EntangledGames_Resampling
import Definitions.Def_OAI_Probability_EntangledGames_EffectExposure
import Definitions.Def_OAI_Probability_EntangledGames_ExposureChain
import Definitions.Def_OAI_Probability_EntangledGames_BlockStates
import Definitions.Def_OAI_Probability_EntangledGames_FreshStates
import Definitions.Def_OAI_Probability_EntangledGames_ExposureData

open OAI OAI.ThresholdParallelRepetition OAI.ThresholdParallelRepetition.MixedExposure OAI.ThresholdParallelRepetition.MixedExposure.EventSystem
universe u_X u_Y u_I u_R u_m u_n
open scoped BigOperators MatrixOrder ComplexOrder
open Matrix
open QuantumSampling Resolvent OperatorEntropy FiniteProbability Law
variable (X : Type u_X) (Y : Type u_Y) (I : Type u_I) (R : Type u_R) (m : Type u_m) (n : Type u_n) [Fintype X] [Fintype Y] [Fintype I]
  [DecidableEq X] [DecidableEq Y] [DecidableEq I]
  [Fintype R] [DecidableEq R] [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
variable {X Y I R m n} [Nonempty X] [Nonempty Y] [Nonempty R]
variable (S : EventSystem X Y I R m n)
section h42
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
variable {α β ι : Type*} [Fintype α] [Fintype β] [Fintype ι] [DecidableEq α] [DecidableEq β] [DecidableEq ι]

lemma h42_bayesL (μ : Law (α×β)) (a₀ : α) (ψ : α×β → ℝ) :
    μ.avg (fun u => (μ.givenSecond a₀ u.2).avg (fun x => ψ (x,u.2))) = μ.avg ψ := by
  simp only [Law.avg, smul_eq_mul, Fintype.sum_prod_type]
  rw [Finset.sum_comm, Finset.sum_comm (f := fun x y => μ.weight (x,y) * ψ (x,y))]
  apply Finset.sum_congr rfl; intro y _
  rw [← Finset.sum_mul]
  by_cases hs : ∑ x, μ.weight (x,y) = 0
  · have h0 : ∀ x, μ.weight (x,y) = 0 := fun x =>
      (Finset.sum_eq_zero_iff_of_nonneg (fun x _ => μ.nonneg (x,y))).mp hs x (Finset.mem_univ _)
    simp [hs, h0]
  · simp only [Law.givenSecond, Law.normalize, dif_neg hs]
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro x _; field_simp

lemma h42_bayesR (μ : Law (α×β)) (b₀ : β) (ψ : α×β → ℝ) :
    μ.avg (fun u => (μ.givenFirst b₀ u.1).avg (fun y => ψ (u.1,y))) = μ.avg ψ := by
  simp only [Law.avg, smul_eq_mul, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl; intro x _
  rw [← Finset.sum_mul]
  by_cases hs : ∑ y, μ.weight (x,y) = 0
  · have h0 : ∀ y, μ.weight (x,y) = 0 := fun y =>
      (Finset.sum_eq_zero_iff_of_nonneg (fun y _ => μ.nonneg (x,y))).mp hs y (Finset.mem_univ _)
    simp [hs, h0]
  · simp only [Law.givenFirst, Law.normalize, dif_neg hs]
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro y _; field_simp

lemma h42_split_apply (k : ι) (u : α×β) (r : {j // j ≠ k} → α×β) :
    ((Equiv.funSplitAt k (α×β)).symm (u,r)) k = u := by
  simp [Equiv.funSplitAt, Equiv.piSplitAt]

lemma h42_left_avg (μ : Law (α×β)) (a₀ : α) (k : ι) (Φ : Profile ι α β → ℝ) :
    (pi (fun _ : ι => μ)).avg (μ.left a₀ k Φ) = (pi (fun _ : ι => μ)).avg Φ := by
  rw [pi_avg_split _ k, pi_avg_split _ k Φ]
  simp only [Law.left, h42_split_apply, Law.updateLeft, update_split]
  rw [← h42_bayesL μ a₀ (fun v => (pi (fun j : {j // j ≠ k} => μ)).avg
    (fun r => Φ ((Equiv.funSplitAt k (α×β)).symm (v,r))))]
  congr 1; funext u
  exact avg_comm _ _ _

lemma h42_right_avg (μ : Law (α×β)) (b₀ : β) (k : ι) (Φ : Profile ι α β → ℝ) :
    (pi (fun _ : ι => μ)).avg (μ.right b₀ k Φ) = (pi (fun _ : ι => μ)).avg Φ := by
  rw [pi_avg_split _ k, pi_avg_split _ k Φ]
  simp only [Law.right, h42_split_apply, Law.updateRight, update_split]
  rw [← h42_bayesR μ b₀ (fun v => (pi (fun j : {j // j ≠ k} => μ)).avg
    (fun r => Φ ((Equiv.funSplitAt k (α×β)).symm (v,r))))]
  congr 1; funext u
  exact avg_comm _ _ _

section h42b
variable {E : Type*} [AddCommMonoid E] [Module ℝ E]
lemma h42_right_ignL (μ : Law (α×β)) (b₀ : β) (k k' : ι) (hk : k ≠ k') (Φ : Profile ι α β → E)
    (h : IgnoresLeft Φ k') : IgnoresLeft (μ.right b₀ k Φ) k' := by
  intro z x
  simp only [Law.right, Law.updateLeft, Law.updateRight, Function.update_of_ne hk]
  congr 1; funext y
  rw [Function.update_comm hk.symm]
  have := h (Function.update z k ((z k).1, y)) x
  simp only [Law.updateLeft, Function.update_of_ne hk.symm] at this
  exact this

lemma h42_left_ignR (μ : Law (α×β)) (a₀ : α) (k k' : ι) (hk : k ≠ k') (Φ : Profile ι α β → E)
    (h : IgnoresRight Φ k') : IgnoresRight (μ.left a₀ k Φ) k' := by
  intro z y
  simp only [Law.left, Law.updateLeft, Law.updateRight, Function.update_of_ne hk]
  congr 1; funext x
  rw [Function.update_comm hk.symm]
  have := h (Function.update z k (x, (z k).2)) y
  simp only [Law.updateRight, Function.update_of_ne hk.symm] at this
  exact this

lemma h42_rights_ignL (μ : Law (α×β)) (b₀ : β) (L : List ι) (k' : ι) (hL : k' ∉ L)
    (Φ : Profile ι α β → E) (h : IgnoresLeft Φ k') : IgnoresLeft (μ.rights b₀ L Φ) k' := by
  induction L with
  | nil => exact h
  | cons k L ih =>
    exact h42_right_ignL μ b₀ k k' (fun e => hL (e ▸ List.mem_cons_self ..))
      _ (ih (fun hm => hL (List.mem_cons_of_mem _ hm)))

lemma h42_lefts_ignR (μ : Law (α×β)) (a₀ : α) (L : List ι) (k' : ι) (hL : k' ∉ L)
    (Φ : Profile ι α β → E) (h : IgnoresRight Φ k') : IgnoresRight (μ.lefts a₀ L Φ) k' := by
  induction L with
  | nil => exact h
  | cons k L ih =>
    exact h42_left_ignR μ a₀ k k' (fun e => hL (e ▸ List.mem_cons_self ..))
      _ (ih (fun hm => hL (List.mem_cons_of_mem _ hm)))

lemma h42_left_upd (μ : Law (α×β)) (a₀ : α) (k i : ι) (hki : k ≠ i) (q : α×β)
    (Φ : Profile ι α β → E) (z : Profile ι α β) :
    μ.left a₀ k Φ (Function.update z i q) = μ.left a₀ k (fun w => Φ (Function.update w i q)) z := by
  simp only [Law.left, Law.updateLeft, Function.update_of_ne hki]
  congr 1; funext x
  rw [Function.update_comm hki]

lemma h42_right_upd (μ : Law (α×β)) (b₀ : β) (k i : ι) (hki : k ≠ i) (q : α×β)
    (Φ : Profile ι α β → E) (z : Profile ι α β) :
    μ.right b₀ k Φ (Function.update z i q) = μ.right b₀ k (fun w => Φ (Function.update w i q)) z := by
  simp only [Law.right, Law.updateRight, Function.update_of_ne hki]
  congr 1; funext x
  rw [Function.update_comm hki]
end h42b

section h42c
variable {m' n' : Type*} [Fintype m'] [Fintype n'] [DecidableEq m'] [DecidableEq n']
lemma h42_prob_left (μ : Law (α×β)) (a₀ : α) (C : Matrix m' n' ℂ) (k : ι) (g : Profile ι α β → ℝ)
    (G : Profile ι α β → Matrix m' m' ℂ) (K : Profile ι α β → Matrix n' n' ℂ)
    (hg : IgnoresLeft g k) (hK : IgnoresLeft K k) (w : Profile ι α β) :
    g w * prob C (μ.left a₀ k G w) (K w) = μ.left a₀ k (fun w => g w * prob C (G w) (K w)) w := by
  simp only [Law.left, Law.avg]
  simp only [show ∀ x, g (updateLeft w k x) = g w from fun x => hg w x,
    show ∀ x, K (updateLeft w k x) = K w from fun x => hK w x]
  rw [prob_sum_left, Finset.mul_sum]; apply Finset.sum_congr rfl; intro x _
  rw [prob_smul_left, smul_eq_mul]; ring

lemma h42_prob_right (μ : Law (α×β)) (b₀ : β) (C : Matrix m' n' ℂ) (k : ι) (g : Profile ι α β → ℝ)
    (F : Profile ι α β → Matrix m' m' ℂ) (H : Profile ι α β → Matrix n' n' ℂ)
    (hg : IgnoresRight g k) (hF : IgnoresRight F k) (w : Profile ι α β) :
    g w * prob C (F w) (μ.right b₀ k H w) = μ.right b₀ k (fun w => g w * prob C (F w) (H w)) w := by
  simp only [Law.right, Law.avg]
  simp only [show ∀ x, g (updateRight w k x) = g w from fun x => hg w x,
    show ∀ x, F (updateRight w k x) = F w from fun x => hF w x]
  rw [prob_sum_right, Finset.mul_sum]; apply Finset.sum_congr rfl; intro x _
  rw [prob_smul_right, smul_eq_mul]; ring

lemma h42_lefts_remove (μ : Law (α×β)) (a₀ : α) (C : Matrix m' n' ℂ) (i : ι) (q : α×β)
    (g : Profile ι α β → ℝ) (K : Profile ι α β → Matrix n' n' ℂ) (F : Profile ι α β → Matrix m' m' ℂ)
    (L : List ι) (hL : ∀ k ∈ L, k ≠ i ∧ IgnoresLeft g k ∧ IgnoresLeft K k) :
    (pi (fun _ : ι => μ)).avg (fun z => g (Function.update z i q) *
      prob C (μ.lefts a₀ L F (Function.update z i q)) (K (Function.update z i q))) =
    (pi (fun _ : ι => μ)).avg (fun z => g (Function.update z i q) *
      prob C (F (Function.update z i q)) (K (Function.update z i q))) := by
  induction L with
  | nil => rfl
  | cons k L ih =>
    obtain ⟨hki, hg, hK⟩ := hL k (List.mem_cons_self ..)
    rw [← ih (fun k' hk' => hL k' (List.mem_cons_of_mem _ hk'))]
    have : ∀ z, g (Function.update z i q) * prob C (μ.lefts a₀ (k::L) F (Function.update z i q))
        (K (Function.update z i q)) = μ.left a₀ k (fun w => (fun w => g w * prob C (μ.lefts a₀ L F w)
          (K w)) (Function.update w i q)) z := by
      intro z; exact (h42_prob_left μ a₀ C k g _ K hg hK _).trans (h42_left_upd μ a₀ k i hki q _ z)
    simp only [this]
    exact h42_left_avg μ a₀ k _

lemma h42_rights_remove (μ : Law (α×β)) (b₀ : β) (C : Matrix m' n' ℂ) (i : ι) (q : α×β)
    (g : Profile ι α β → ℝ) (F : Profile ι α β → Matrix m' m' ℂ) (H : Profile ι α β → Matrix n' n' ℂ)
    (L : List ι) (hL : ∀ k ∈ L, k ≠ i ∧ IgnoresRight g k ∧ IgnoresRight F k) :
    (pi (fun _ : ι => μ)).avg (fun z => g (Function.update z i q) *
      prob C (F (Function.update z i q)) (μ.rights b₀ L H (Function.update z i q))) =
    (pi (fun _ : ι => μ)).avg (fun z => g (Function.update z i q) *
      prob C (F (Function.update z i q)) (H (Function.update z i q))) := by
  induction L with
  | nil => rfl
  | cons k L ih =>
    obtain ⟨hki, hg, hF⟩ := hL k (List.mem_cons_self ..)
    rw [← ih (fun k' hk' => hL k' (List.mem_cons_of_mem _ hk'))]
    have : ∀ z, g (Function.update z i q) * prob C (F (Function.update z i q))
        (μ.rights b₀ (k::L) H (Function.update z i q)) = μ.right b₀ k (fun w => (fun w => g w *
          prob C (F w) (μ.rights b₀ L H w)) (Function.update w i q)) z := by
      intro z; exact (h42_prob_right μ b₀ C k g F _ hg hF _).trans (h42_right_upd μ b₀ k i hki q _ z)
    simp only [this]
    exact h42_right_avg μ b₀ k _
end h42c
end h42

section h42d
set_option linter.unusedSectionVars false
lemma h42_hsSq_wb {p₁ p₂ T : Type*} [Fintype p₁] [Fintype p₂] [Fintype T] [DecidableEq T]
    (w : T → ℝ) (hw : ∀ t, 0 ≤ w t) (M : T → Matrix p₁ p₂ ℂ) :
    hsSq (weightedBlock w M) = ∑ t, w t * hsSq (M t) := by
  simp only [hsSq, weightedBlock, Fintype.sum_prod_type, Matrix.blockDiagonal_apply]
  simp only [apply_ite Complex.normSq, map_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true,
    Matrix.smul_apply, Complex.real_smul, Complex.normSq_mul, Complex.normSq_ofReal,
    Real.mul_self_sqrt (hw _)]
  rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro t _
  rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro a _
  rw [Finset.mul_sum]

lemma h42_hsSq_trace {p₁ p₂ : Type*} [Fintype p₁] [Fintype p₂] (N : Matrix p₁ p₂ ℂ) :
    hsSq N = (Matrix.trace (Nᴴ*N)).re := by
  simp only [hsSq, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Complex.re_sum]
  rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl; intro j _
  rw [Complex.normSq_apply]; simp

lemma h42_hsSq_UCV {p₁ p₂ m' n' : Type*} [Fintype p₁] [Fintype p₂] [Fintype m'] [Fintype n']
    (U : Matrix p₁ m' ℂ) (C : Matrix m' n' ℂ) (V : Matrix p₂ n' ℂ) :
    hsSq (U*C*Vᵀ) = prob C (Uᴴ*U) (Vᴴ*V) := by
  rw [h42_hsSq_trace, prob, eval_eq_trace]
  congr 1
  have e : (Vᵀ)ᴴ = (Vᴴ)ᵀ := by ext; simp
  simp only [Matrix.conjTranspose_mul, Matrix.transpose_mul, Matrix.mul_assoc, e]
  rw [Matrix.trace_mul_comm]; simp only [Matrix.mul_assoc]
end h42d
lemma h42_idx {ι : Type*} (l : List ι) (hl : l.Nodup) (j : ℕ) (hj : j < l.length) :
    l[j] ∉ l.drop (j+1) ∧ l[j] ∉ l.take j ∧ ∀ k ∈ l.drop (j+1), k ∉ l.take j := by
  have e : l = l.take j ++ (l[j] :: l.drop (j+1)) := by simp
  rw [e] at hl
  rw [List.nodup_append] at hl
  obtain ⟨h1, h2, h3⟩ := hl
  rw [List.nodup_cons] at h2
  refine ⟨h2.1, fun h => h3 _ h _ List.mem_cons_self rfl, fun k hk hk' => h3 _ hk' _ (List.mem_cons_of_mem _ hk) rfl⟩
lemma h42_rev {ι : Type*} (l : List ι) (j : ℕ) (hj : j < l.length) :
    (l.take (j+1)).reverse = l[j] :: (l.take j).reverse := by
  rw [List.take_add_one, List.getElem?_eq_getElem hj]; simp

lemma h42_avg_mul {α : Type*} [Fintype α] (p : Law α) (c : ℝ) (f : α → ℝ) :
    p.avg (fun x => c * f x) = c * p.avg f := by
  simp only [Law.avg, smul_eq_mul, Finset.mul_sum]; apply Finset.sum_congr rfl; intro x _; ring

lemma h42_ign_both {α β ι E : Type*} [DecidableEq ι] (g : Profile ι α β → E) (i : ι)
    (hL : IgnoresLeft g i) (hR : IgnoresRight g i) (z : Profile ι α β) (q : α×β) :
    g (Function.update z i q) = g z := by
  have := hR (updateLeft z i q.1) q.2
  simp only [Law.updateRight, Law.updateLeft, Function.update_self, Function.update_idem] at this
  rw [this]; exact hL z q.1

theorem solution (j : Fin S.l.length) (x : X) : hsSq (S.rawA j x) =
    (S.μ.givenFirst S.y₀ x).avg (fun y => coordDensity (fun _ : I => S.μ) S.density S.l[j.val] (x,y)) := by
  obtain ⟨hd, ht, hdt⟩ := h42_idx S.l S.nodup j.val j.isLt
  have hrev := h42_rev S.l j.val j.isLt
  set i := S.l[j.val] with hi_def
  have hiL : i ∈ S.l := List.getElem_mem _
  -- LHS
  rw [EventSystem.rawA]
  simp only [stateAt]
  rw [h42_hsSq_wb _ (fun t => by
    have := (pi (fun _ : I => S.μ)).nonneg t.2; have := S.hθ t.1 t.2; have := S.hp; positivity)]
  simp only [h42_hsSq_UCV, S.U_gram (show j.val+1 ≤ S.l.length by omega),
    S.V_gram (show j.val+1 ≤ S.l.length by omega)]
  simp only [← hi_def]
  have hterm : ∀ r z, S.θ r z * prob S.C (S.f (j.val+1) r (Function.update z i (x,S.y₀)))
      (S.h (j.val+1) r (Function.update z i (x,S.y₀))) =
      (S.μ.givenFirst S.y₀ x).avg (fun y => S.θ r (Function.update z i (x,y)) *
        prob S.C (S.f (j.val+1) r (Function.update z i (x,y))) (S.h j.val r (Function.update z i (x,y)))) := by
    intro r z
    have hh : S.h (j.val+1) r (Function.update z i (x,S.y₀)) =
        (S.μ.givenFirst S.y₀ x).avg (fun y => S.h j.val r (Function.update z i (x,y))) := by
      show S.μ.rights S.y₀ (S.l.take (j.val+1)).reverse (S.H r) _ = _
      rw [hrev]
      show S.μ.right S.y₀ i (S.μ.rights S.y₀ (S.l.take j.val).reverse (S.H r)) _ = _
      simp only [Law.right, Law.updateRight, Function.update_self, Function.update_idem]
      rfl
    rw [hh]
    simp only [Law.avg, prob_sum_right, prob_smul_right, Finset.mul_sum, smul_eq_mul]
    apply Finset.sum_congr rfl; intro y _
    rw [h42_ign_both (S.θ r) i (S.localθL r i hiL) (S.localθR r i hiL)]
    have hign : IgnoresRight (S.f (j.val+1) r) i :=
      h42_lefts_ignR S.μ S.x₀ _ i hd (S.F r) (S.localF r i)
    have hf : S.f (j.val+1) r (Function.update z i (x,y)) =
        S.f (j.val+1) r (Function.update z i (x,S.y₀)) := by
      have := hign (Function.update z i (x,S.y₀)) y
      simpa [Law.updateRight, Function.update_idem] using this
    rw [hf]; ring
  rw [Fintype.sum_prod_type]
  have hL : ∀ r, ∑ z, (pi (fun _ : I => S.μ)).weight z * S.θ r z / S.p *
      prob S.C (S.f (j.val+1) r (Function.update z i (x,S.y₀)))
        (S.h (j.val+1) r (Function.update z i (x,S.y₀))) =
      (1/S.p) * (pi (fun _ : I => S.μ)).avg (fun z => S.θ r z *
        prob S.C (S.f (j.val+1) r (Function.update z i (x,S.y₀)))
          (S.h (j.val+1) r (Function.update z i (x,S.y₀)))) := by
    intro r; simp only [Law.avg, smul_eq_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro z _; ring
  simp only [hL, hterm]
  have hR : (S.μ.givenFirst S.y₀ x).avg (fun y => coordDensity (fun _ : I => S.μ) S.density i (x,y)) =
      ∑ r, (1/S.p) * (S.μ.givenFirst S.y₀ x).avg (fun y => (pi (fun _ : I => S.μ)).avg (fun z =>
        S.θ r (Function.update z i (x,y)) * prob S.C (S.F r (Function.update z i (x,y)))
          (S.H r (Function.update z i (x,y))))) := by
    simp only [coordDensity, EventSystem.density, eventDensity, h42_avg_mul, Law.avg_sum, Finset.mul_sum]
  rw [hR]
  apply Finset.sum_congr rfl; intro r _
  congr 1
  rw [Law.avg_comm]
  congr 1; funext y
  have hL1 : ∀ k ∈ S.l.drop (j.val+1), k ≠ i ∧ IgnoresLeft (S.θ r) k ∧ IgnoresLeft (S.h j.val r) k :=
    fun k hk => ⟨fun e => hd (e ▸ hk), S.localθL r k (List.mem_of_mem_drop hk),
      h42_rights_ignL S.μ S.y₀ _ k (by rw [List.mem_reverse]; exact hdt k hk) (S.H r) (S.localH r k)⟩
  have hL2 : ∀ k ∈ (S.l.take j.val).reverse, k ≠ i ∧ IgnoresRight (S.θ r) k ∧ IgnoresRight (S.F r) k := by
    intro k hk; rw [List.mem_reverse] at hk
    exact ⟨fun e => ht (e ▸ hk), S.localθR r k (List.mem_of_mem_take hk), S.localF r k⟩
  exact (h42_lefts_remove S.μ S.x₀ S.C i (x,y) (S.θ r) (S.h j.val r) (S.F r) _ hL1).trans
    (h42_rights_remove S.μ S.y₀ S.C i (x,y) (S.θ r) (S.F r) (S.H r) _ hL2)

