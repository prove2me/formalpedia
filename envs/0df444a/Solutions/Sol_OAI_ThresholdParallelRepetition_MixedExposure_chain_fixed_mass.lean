-- Prove2me | solution 1 for OAI.ThresholdParallelRepetition.MixedExposure.chain_fixed_mass
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T12:29:02.37706+00:00
-- url     : https://prove2.me/submissions/79d5360d-b85e-4867-b84a-ce667d9c9a83

-- Generated from openai/math@1581d4c lean/OAI/Probability/EntangledGames/FreshStates.lean:L144-L171
-- (upload_full_project.md Phase 4): solution for node OAI.ThresholdParallelRepetition.MixedExposure.chain_fixed_mass. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
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
import Theorems.Thm_OAI_ThresholdParallelRepetition_FiniteProbability_Law_pi_avg_left
import Theorems.Thm_OAI_ThresholdParallelRepetition_FiniteProbability_Law_pi_avg_right

-- ---- from OAI.Probability.EntangledGames.FiniteProbability ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe u_α u_β u_γ u_E u_F u_ι

noncomputable section
open scoped BigOperators
namespace ThresholdParallelRepetition.FiniteProbability

namespace Law
variable {α : Type u_α} {β : Type u_β} {γ : Type u_γ} {E : Type u_E} [Fintype α] [Fintype β] [Fintype γ]
  [AddCommMonoid E] [Module ℝ E]

lemma avg_linear (p : Law α) (f : α → E) {F : Type u_F} [AddCommMonoid F] [Module ℝ F]
    (L : E →ₗ[ℝ] F) : L (p.avg f) = p.avg (fun x => L (f x)) := by
  simp [avg]

section Pair
variable [DecidableEq α] [DecidableEq β]

end Pair

section Pi
variable {ι : Type u_ι} [Fintype ι] [DecidableEq ι]

end Pi

section Information

variable {ι : Type u_ι} [Fintype ι] [DecidableEq ι] [DecidableEq α]
end Information

end Law
end ThresholdParallelRepetition.FiniteProbability

end

end OAI

-- ---- from OAI.Probability.EntangledGames.Resampling ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe u_X u_Y u_I u_E u_F u_R

noncomputable section
open scoped BigOperators
namespace ThresholdParallelRepetition.FiniteProbability
namespace Law
variable {X : Type u_X} {Y : Type u_Y} {I : Type u_I} {E : Type u_E} [Fintype X] [Fintype Y] [Fintype I] [DecidableEq I]
  [DecidableEq X] [DecidableEq Y] [AddCommMonoid E] [Module ℝ E]

omit [Fintype X] [Fintype Y] [Fintype I] [DecidableEq X] [DecidableEq Y] in
lemma updateLeft_right_comm (z : Profile I X Y) (i j : I) (x : X) (y : Y) :
    updateLeft (updateRight z j y) i x = updateRight (updateLeft z i x) j y := by
  by_cases hij : i = j
  · subst j; simp [updateLeft, updateRight]
  · simp only [updateLeft, updateRight, Function.update_of_ne hij,
      Function.update_of_ne (Ne.symm hij)]
    exact Function.update_comm (Ne.symm hij) _ _ z

omit [Fintype I] [DecidableEq X] in
lemma right_ignoresLeft_other (μ : Law (X×Y)) (y₀ : Y) {i j : I} (hij : i ≠ j)
    {f : Profile I X Y → E} (hf : IgnoresLeft f j) : IgnoresLeft (μ.right y₀ i f) j := by
  intro z x
  have hi : updateLeft z j x i = z i := Function.update_of_ne hij _ _
  simp only [right, hi]
  congr 1
  funext u
  rw [← updateLeft_right_comm, hf _ _]

section Linear
variable {F : Type u_F} [AddCommMonoid F] [Module ℝ F]
omit [Fintype I] [DecidableEq Y] in
lemma left_linear (μ : Law (X×Y)) (x₀ : X) (i : I)
    (f : Profile I X Y → E) (L : E →ₗ[ℝ] F) (z : Profile I X Y) :
    L (μ.left x₀ i f z) = μ.left x₀ i (fun q => L (f q)) z := avg_linear _ _ _
omit [Fintype I] [DecidableEq X] in
lemma right_linear (μ : Law (X×Y)) (y₀ : Y) (i : I)
    (f : Profile I X Y → E) (L : E →ₗ[ℝ] F) (z : Profile I X Y) :
    L (μ.right y₀ i f z) = μ.right y₀ i (fun q => L (f q)) z := avg_linear _ _ _

omit [DecidableEq Y] in
lemma pi_left_pairing (μ : Law (X×Y)) (x₀ : X) (i : I) (f : Profile I X Y → E)
    (L : Profile I X Y → E →ₗ[ℝ] F) (hL : IgnoresLeft L i) :
    (pi (fun _ : I => μ)).avg (fun z => L z (μ.left x₀ i f z)) =
      (pi (fun _ : I => μ)).avg (fun z => L z (f z)) := by
  have he : (fun z => L z (μ.left x₀ i f z)) =
      μ.left x₀ i (fun z => L z (f z)) := by
    funext z
    rw [left_linear]
    unfold left
    congr 1
    funext x
    simp only [hL z x]
  rw [he, pi_avg_left]

omit [DecidableEq X] in
lemma pi_right_pairing (μ : Law (X×Y)) (y₀ : Y) (i : I) (f : Profile I X Y → E)
    (L : Profile I X Y → E →ₗ[ℝ] F) (hL : IgnoresRight L i) :
    (pi (fun _ : I => μ)).avg (fun z => L z (μ.right y₀ i f z)) =
      (pi (fun _ : I => μ)).avg (fun z => L z (f z)) := by
  have he : (fun z => L z (μ.right y₀ i f z)) =
      μ.right y₀ i (fun z => L z (f z)) := by
    funext z
    rw [right_linear]
    unfold right
    congr 1
    funext y
    simp only [hL z y]
  rw [he, pi_avg_right]
end Linear

section Folds

omit [Fintype I] [DecidableEq X] in
lemma rights_ignoresLeft_notMem (μ : Law (X×Y)) (y₀ : Y) (l : List I)
    {f : Profile I X Y → E} {i : I} (hi : i ∉ l) (hf : IgnoresLeft f i) :
    IgnoresLeft (μ.rights y₀ l f) i := by
  induction l with
  | nil => exact hf
  | cons j l ih =>
    have h : i ≠ j ∧ i ∉ l := by simpa only [List.mem_cons, not_or] using hi
    exact right_ignoresLeft_other μ y₀ (Ne.symm h.1) (ih h.2)

variable {F : Type u_F} [AddCommMonoid F] [Module ℝ F]
end Folds

section FixedCoordinate
omit [Fintype X] [Fintype Y] [Fintype I] [DecidableEq X] [DecidableEq Y] in
lemma updateLeft_update (z : Profile I X Y) {i j : I} (hij : i ≠ j)
    (q : X×Y) (x : X) :
    updateLeft (Function.update z i q) j x = Function.update (updateLeft z j x) i q := by
  simp only [updateLeft, Function.update_of_ne (Ne.symm hij)]
  exact Function.update_comm hij _ _ z
omit [Fintype X] [Fintype Y] [Fintype I] [DecidableEq X] [DecidableEq Y] in
lemma updateRight_update (z : Profile I X Y) {i j : I} (hij : i ≠ j)
    (q : X×Y) (y : Y) :
    updateRight (Function.update z i q) j y = Function.update (updateRight z j y) i q := by
  simp only [updateRight, Function.update_of_ne (Ne.symm hij)]
  exact Function.update_comm hij _ _ z

omit [Fintype I] [DecidableEq Y] in
lemma left_update (μ : Law (X×Y)) (x₀ : X) {i j : I} (hij : i ≠ j)
    (f : Profile I X Y → E) (z : Profile I X Y) (q : X×Y) :
    μ.left x₀ j f (Function.update z i q) =
      μ.left x₀ j (fun r => f (Function.update r i q)) z := by
  simp only [left, Function.update_of_ne (Ne.symm hij), updateLeft_update _ hij]
omit [Fintype I] [DecidableEq X] in
lemma right_update (μ : Law (X×Y)) (y₀ : Y) {i j : I} (hij : i ≠ j)
    (f : Profile I X Y → E) (z : Profile I X Y) (q : X×Y) :
    μ.right y₀ j f (Function.update z i q) =
      μ.right y₀ j (fun r => f (Function.update r i q)) z := by
  simp only [right, Function.update_of_ne (Ne.symm hij), updateRight_update _ hij]

variable {F : Type u_F} [AddCommMonoid F] [Module ℝ F]
omit [DecidableEq Y] in
lemma pi_fixed_left_pairing (μ : Law (X×Y)) (x₀ : X) {i j : I} (hij : i ≠ j)
    (q : X×Y) (f : Profile I X Y → E)
    (L : Profile I X Y → E →ₗ[ℝ] F) (hL : IgnoresLeft L j) :
    (pi (fun _ : I => μ)).avg (fun z => L (Function.update z i q)
      (μ.left x₀ j f (Function.update z i q))) =
    (pi (fun _ : I => μ)).avg (fun z => L (Function.update z i q) (f (Function.update z i q))) := by
  simp_rw [left_update μ x₀ hij]
  apply pi_left_pairing
  intro z x
  dsimp only
  rw [← updateLeft_update _ hij, hL]
omit [DecidableEq X] in
lemma pi_fixed_right_pairing (μ : Law (X×Y)) (y₀ : Y) {i j : I} (hij : i ≠ j)
    (q : X×Y) (f : Profile I X Y → E)
    (L : Profile I X Y → E →ₗ[ℝ] F) (hL : IgnoresRight L j) :
    (pi (fun _ : I => μ)).avg (fun z => L (Function.update z i q)
      (μ.right y₀ j f (Function.update z i q))) =
    (pi (fun _ : I => μ)).avg (fun z => L (Function.update z i q) (f (Function.update z i q))) := by
  simp_rw [right_update μ y₀ hij]
  apply pi_right_pairing
  intro z y
  dsimp only
  rw [← updateRight_update _ hij, hL]

omit [DecidableEq Y] in
lemma pi_fixed_lefts_pairing (μ : Law (X×Y)) (x₀ : X) (l : List I) {i : I} (hi : i ∉ l)
    (q : X×Y) (f : Profile I X Y → E)
    (L : Profile I X Y → E →ₗ[ℝ] F) (hL : ∀ j ∈ l, IgnoresLeft L j) :
    (pi (fun _ : I => μ)).avg (fun z => L (Function.update z i q)
      (μ.lefts x₀ l f (Function.update z i q))) =
    (pi (fun _ : I => μ)).avg (fun z => L (Function.update z i q) (f (Function.update z i q))) := by
  induction l with
  | nil => rfl
  | cons j l ih =>
    have hn : i ≠ j ∧ i ∉ l := by simpa only [List.mem_cons, not_or] using hi
    change (pi _).avg (fun z => L (Function.update z i q)
      (μ.left x₀ j (μ.lefts x₀ l f) (Function.update z i q))) = _
    rw [pi_fixed_left_pairing μ x₀ hn.1 q _ L (hL j List.mem_cons_self)]
    exact ih hn.2 (fun t ht => hL t (List.mem_cons_of_mem j ht))
omit [DecidableEq X] in
lemma pi_fixed_rights_pairing (μ : Law (X×Y)) (y₀ : Y) (l : List I) {i : I} (hi : i ∉ l)
    (q : X×Y) (f : Profile I X Y → E)
    (L : Profile I X Y → E →ₗ[ℝ] F) (hL : ∀ j ∈ l, IgnoresRight L j) :
    (pi (fun _ : I => μ)).avg (fun z => L (Function.update z i q)
      (μ.rights y₀ l f (Function.update z i q))) =
    (pi (fun _ : I => μ)).avg (fun z => L (Function.update z i q) (f (Function.update z i q))) := by
  induction l with
  | nil => rfl
  | cons j l ih =>
    have hn : i ≠ j ∧ i ∉ l := by simpa only [List.mem_cons, not_or] using hi
    change (pi _).avg (fun z => L (Function.update z i q)
      (μ.right y₀ j (μ.rights y₀ l f) (Function.update z i q))) = _
    rw [pi_fixed_right_pairing μ y₀ hn.1 q _ L (hL j List.mem_cons_self)]
    exact ih hn.2 (fun t ht => hL t (List.mem_cons_of_mem j ht))
end FixedCoordinate

section FoldLinear
variable {R : Type u_R} {F : Type u_F} [Fintype R] [AddCommMonoid F] [Module ℝ F]
end FoldLinear

end Law
end ThresholdParallelRepetition.FiniteProbability

end

end OAI

-- ---- from OAI.Probability.EntangledGames.MixedExposure ----
namespace OAI

universe u_X u_Y u_I u_m u_n u_J u_K

noncomputable section
open scoped BigOperators MatrixOrder ComplexOrder
open Matrix
namespace ThresholdParallelRepetition.MixedExposure
open QuantumSampling Resolvent OperatorEntropy FiniteProbability Law
variable {X : Type u_X} {Y : Type u_Y} {I : Type u_I} {m : Type u_m} {n : Type u_n} {J : Type u_J} {K : Type u_K} [Fintype X] [Fintype Y] [Fintype I]
  [DecidableEq X] [DecidableEq Y] [DecidableEq I]
  [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
  [Fintype J] [DecidableEq J] [Nonempty J] [Fintype K] [DecidableEq K] [Nonempty K]

end ThresholdParallelRepetition.MixedExposure

end

noncomputable section
open scoped BigOperators MatrixOrder ComplexOrder
open Matrix
namespace ThresholdParallelRepetition.MixedExposure
open QuantumSampling Resolvent OperatorEntropy FiniteProbability Law
variable {X : Type u_X} {Y : Type u_Y} {I : Type u_I} {m : Type u_m} {n : Type u_n} [Fintype X] [Fintype Y] [Fintype I]
  [DecidableEq X] [DecidableEq Y] [DecidableEq I]
  [Fintype m] [Fintype n]

lemma fixed_mixed_pairing (μ : Law (X×Y)) (x₀ : X) (y₀ : Y) (l r : List I)
    (hlr : ∀ i ∈ l, i ∉ r) (C : Matrix m n ℂ)
    (F : Profile I X Y → Matrix m m ℂ) (H : Profile I X Y → Matrix n n ℂ)
    (hF : ∀ i ∈ r, IgnoresRight F i) (hH : ∀ i ∈ l, IgnoresLeft H i)
    (θ : Profile I X Y → ℝ) (hθL : ∀ i ∈ l, IgnoresLeft θ i) (hθR : ∀ i ∈ r, IgnoresRight θ i)
    (i : I) (hiL : i ∉ l) (hiR : i ∉ r) (q : X×Y) :
    (pi (fun _ : I => μ)).avg (fun z => θ (Function.update z i q) * prob C
      (μ.lefts x₀ l F (Function.update z i q)) (μ.rights y₀ r H (Function.update z i q))) =
    (pi (fun _ : I => μ)).avg (fun z => θ (Function.update z i q) *
      prob C (F (Function.update z i q)) (H (Function.update z i q))) := by
  calc
    _ = (pi (fun _ : I => μ)).avg (fun z => θ (Function.update z i q) *
        prob C (F (Function.update z i q)) (μ.rights y₀ r H (Function.update z i q))) := by
      apply pi_fixed_lefts_pairing μ x₀ l hiL q F (fun z => θ z • probLeft C (μ.rights y₀ r H z))
      intro j hj z x
      simp only [hθL j hj z, rights_ignoresLeft_notMem μ y₀ r (hlr j hj) (hH j hj) z]
    _ = _ := by
      apply pi_fixed_rights_pairing μ y₀ r hiR q H (fun z => θ z • probRight C (F z))
      intro j hj z y
      simp only [hθR j hj z, hF j hj z]
end ThresholdParallelRepetition.MixedExposure

end

end OAI

-- ---- from OAI.Probability.EntangledGames.ExposureChain ----
namespace OAI

universe u_I u_X u_Y u_R u_m u_n u_E u_Z

noncomputable section
open scoped BigOperators MatrixOrder ComplexOrder
open Matrix
namespace ThresholdParallelRepetition.MixedExposure
open QuantumSampling Resolvent OperatorEntropy FiniteProbability Law

lemma list_suffix_prefix_disjoint {I : Type u_I} (l : List I) (hN : l.Nodup) (j : ℕ) :
    ∀ i ∈ l.drop j, i ∉ (l.take j).reverse := by
  have h : (l.take j ++ l.drop j).Nodup := by simpa using hN
  have hd := (List.nodup_append.mp h).2.2
  intro i hi hi'
  exact hd i (List.mem_reverse.mp hi') i hi rfl

lemma list_fresh_not_suffix {I : Type u_I} (l : List I) (hN : l.Nodup) (j : ℕ)
    (hj : j < l.length) : l[j] ∉ l.drop (j+1) := by
  have h : (l.drop j).Nodup := hN.drop
  rw [List.drop_eq_getElem_cons hj] at h
  exact (List.nodup_cons.mp h).1

lemma list_fresh_not_prefix {I : Type u_I} (l : List I) (hN : l.Nodup) (j : ℕ)
    (hj : j < l.length) : l[j] ∉ (l.take j).reverse := by
  apply list_suffix_prefix_disjoint l hN j l[j]
  rw [List.drop_eq_getElem_cons hj]
  exact List.mem_cons_self

variable {X : Type u_X} {Y : Type u_Y} {I : Type u_I} {R : Type u_R} {m : Type u_m} {n : Type u_n} [Fintype X] [Fintype Y] [Fintype I]
  [DecidableEq X] [DecidableEq Y] [DecidableEq I]
  [Fintype R] [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]

variable {E : Type u_E} [AddCommMonoid E] [Module ℝ E]
end ThresholdParallelRepetition.MixedExposure

end

noncomputable section
open scoped BigOperators MatrixOrder ComplexOrder
open Matrix
namespace ThresholdParallelRepetition.MixedExposure
open QuantumSampling Resolvent OperatorEntropy FiniteProbability Law
variable {R : Type u_R} {Z : Type u_Z} {m : Type u_m} {n : Type u_n} [Fintype R] [Nonempty R] [Fintype Z]
  [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]

end ThresholdParallelRepetition.MixedExposure

end

noncomputable section
open scoped BigOperators MatrixOrder ComplexOrder
open Matrix
namespace ThresholdParallelRepetition.MixedExposure
open QuantumSampling Resolvent OperatorEntropy FiniteProbability Law
variable {X : Type u_X} {Y : Type u_Y} {I : Type u_I} {R : Type u_R} {m : Type u_m} {n : Type u_n} [Fintype X] [Fintype Y] [Fintype I]
  [DecidableEq X] [DecidableEq Y] [DecidableEq I] [Nonempty X] [Nonempty Y]
  [Fintype R] [DecidableEq R] [Nonempty R]
  [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]

end ThresholdParallelRepetition.MixedExposure

end

noncomputable section
open scoped BigOperators MatrixOrder ComplexOrder
open Matrix
namespace ThresholdParallelRepetition.MixedExposure
open QuantumSampling OperatorEntropy FiniteProbability Law
variable {X : Type u_X} {Y : Type u_Y} {I : Type u_I} {R : Type u_R} {m : Type u_m} {n : Type u_n} [Fintype X] [Fintype Y] [Fintype I] [DecidableEq I]
  [Fintype R] [DecidableEq X] [DecidableEq Y]
  [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

end ThresholdParallelRepetition.MixedExposure

end

end OAI

-- ---- from OAI.Probability.EntangledGames.FreshStates ----
namespace OAI

universe u_X u_Y u_I u_E u_R u_m u_n u_u u_v u_Z

noncomputable section
open scoped BigOperators MatrixOrder ComplexOrder
open Matrix
namespace ThresholdParallelRepetition.FiniteProbability.Law
variable {X : Type u_X} {Y : Type u_Y} {I : Type u_I} {E : Type u_E} [DecidableEq I]
lemma ignoresRight_update {f : Profile I X Y → E} {i : I} (hf : IgnoresRight f i)
    (z : Profile I X Y) (x : X) (y y' : Y) :
    f (Function.update z i (x,y)) = f (Function.update z i (x,y')) := by
  simpa [updateRight] using hf (Function.update z i (x,y')) y
lemma ignores_update {f : Profile I X Y → E} {i : I} (hL : IgnoresLeft f i) (hR : IgnoresRight f i)
    (z : Profile I X Y) (q : X×Y) : f (Function.update z i q) = f z := by
  obtain ⟨x,y⟩ := q
  rw [ignoresRight_update hR z x y (z i).2]
  exact hL z x
end ThresholdParallelRepetition.FiniteProbability.Law
namespace ThresholdParallelRepetition.MixedExposure
open QuantumSampling FiniteProbability Law
variable {X : Type u_X} {Y : Type u_Y} {I : Type u_I} {R : Type u_R} [Fintype X] [Fintype Y] [Fintype I] [DecidableEq I]
  [Fintype R] [DecidableEq R] [DecidableEq X] [DecidableEq Y]
variable {m : Type u_m} {n : Type u_n} {u : Type u_u} {v : Type u_v} [Fintype m] [Fintype n] [Fintype u] [Fintype v]
variable [DecidableEq m] [DecidableEq n] [DecidableEq u] [DecidableEq v]
end ThresholdParallelRepetition.MixedExposure

end

noncomputable section
open scoped BigOperators MatrixOrder ComplexOrder
open Matrix
namespace ThresholdParallelRepetition.MixedExposure
open QuantumSampling Resolvent OperatorEntropy FiniteProbability Law
variable {X : Type u_X} {Y : Type u_Y} {I : Type u_I} {R : Type u_R} {m : Type u_m} {n : Type u_n} [Fintype X] [Fintype Y] [Fintype I]
  [DecidableEq X] [DecidableEq Y] [DecidableEq I]
  [Fintype R] [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]

omit [DecidableEq m] [DecidableEq n] in
lemma chain_fixed_mass (μ : Law (X×Y)) (x₀ : X) (y₀ : Y) (l : List I) (hN : l.Nodup)
    (C : Matrix m n ℂ) (F : R → Profile I X Y → Matrix m m ℂ)
    (H : R → Profile I X Y → Matrix n n ℂ)
    (hF : ∀ r i, IgnoresRight (F r) i) (hH : ∀ r i, IgnoresLeft (H r) i)
    (θ : R → Profile I X Y → ℝ)
    (hθL : ∀ r i, i ∈ l → IgnoresLeft (θ r) i) (hθR : ∀ r i, i ∈ l → IgnoresRight (θ r) i)
    (p : ℝ) (j : Fin l.length) (q : X×Y) :
    massAt μ θ p l[j.val] C (chainLeft μ x₀ l F (j+1)) (chainRight μ y₀ l H j) q =
      massAt μ θ p l[j.val] C F H q := by
  unfold massAt
  congr 1
  apply Finset.sum_congr rfl; intro r _
  have hθi (z : Profile I X Y) : θ r (Function.update z l[j.val] q) = θ r z :=
    ignores_update (hθL r _ (List.getElem_mem j.isLt)) (hθR r _ (List.getElem_mem j.isLt)) z q
  have he (G : Profile I X Y → ℝ) :
      (pi (fun _ : I => μ)).avg (fun z => θ r z*G (Function.update z l[j.val] q)) =
      (pi (fun _ : I => μ)).avg (fun z => θ r (Function.update z l[j.val] q)*G (Function.update z l[j.val] q)) := by
    simp only [hθi]
  rw [he (fun z => prob C (chainLeft μ x₀ l F (j+1) r z) (chainRight μ y₀ l H j r z)),
    he (fun z => prob C (F r z) (H r z))]
  apply fixed_mixed_pairing μ x₀ y₀ _ _ _ C (F r) (H r)
    (fun i _ => hF r i) (fun i _ => hH r i) (θ r)
    (fun i hi => hθL r i (List.mem_of_mem_drop hi))
    (fun i hi => hθR r i (List.mem_of_mem_take (List.mem_reverse.mp hi)))
    l[j.val] (list_fresh_not_suffix l hN j j.isLt) (list_fresh_not_prefix l hN j j.isLt) q
  intro i hi
  exact list_suffix_prefix_disjoint l hN j i (List.drop_subset_drop_left l (Nat.le_succ j) hi)

end ThresholdParallelRepetition.MixedExposure

end

noncomputable section
open scoped BigOperators MatrixOrder ComplexOrder
open Matrix
namespace ThresholdParallelRepetition.QuantumSampling
-- [generator] trimmed: open FiniteProbability Law ScalarEntropy
open FiniteProbability Law
variable {m : Type u_m} {n : Type u_n} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
variable {X : Type u_X} {Y : Type u_Y} [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
end ThresholdParallelRepetition.QuantumSampling

end

end OAI

-- ---- platform node ----
open OAI OAI.ThresholdParallelRepetition OAI.ThresholdParallelRepetition.MixedExposure
open scoped BigOperators MatrixOrder ComplexOrder
open Matrix
open QuantumSampling Resolvent OperatorEntropy FiniteProbability Law


theorem solution.{u_X,u_Y,u_I,u_R,u_m,u_n} : type_of% @_root_.OAI.ThresholdParallelRepetition.MixedExposure.chain_fixed_mass.{u_X,u_Y,u_I,u_R,u_m,u_n} := @_root_.OAI.ThresholdParallelRepetition.MixedExposure.chain_fixed_mass.{u_X,u_Y,u_I,u_R,u_m,u_n}
