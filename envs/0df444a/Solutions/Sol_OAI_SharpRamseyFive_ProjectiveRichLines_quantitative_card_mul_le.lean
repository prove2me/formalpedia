-- Prove2me | solution 1 for OAI.SharpRamseyFive.ProjectiveRichLines.quantitative_card_mul_le
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T00:08:08.555264+00:00
-- url     : https://prove2.me/submissions/36424844-6c95-4633-baa0-074f0fadca4e

import Mathlib
import Definitions.Def_OAIQ060R000
import Definitions.Def_OAIQ060R001

section
-- module Solutions.OAIQ060_R5.RamseyFive_Decoding_CoordinateMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open scoped BigOperators
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal
namespace SharpRamseyFive.ScalarExtension
open scoped LinearAlgebra.Projectivization
variable {K L I : Type*} [Field K] [Field L] [Algebra K L]

lemma coordinateMap_injective : Function.Injective (coordinateMap (K := K) (L := L) (I := I)) := by
  intro u v h
  ext i
  exact (algebraMap K L).injective (congrFun h i)

lemma coordinateMap_ne_zero (v : I → K) (hv : v ≠ 0) :
    coordinateMap (L := L) v ≠ 0 := by
  intro h
  apply hv
  apply coordinateMap_injective (L := L)
  simpa using h

end SharpRamseyFive.ScalarExtension

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Decoding_PairExpBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open scoped BigOperators
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal
namespace SharpRamseyFive.RichParameters

lemma pair_exp_bound {N M J : ℕ} (hM : 2 ≤ M) (hMN : M ≤ N)
    (hpack : J * (M*(M-1)) ≤ N^2) :
    (J:ℝ)*Real.exp (-(256/3:ℝ)*Real.sqrt ((N:ℝ)/M)) < 1/2 := by
  have hMp : (0:ℝ) < M := by exact_mod_cast lt_of_lt_of_le (by decide : 0<2) hM
  have hM2 : (2:ℝ) ≤ M := by exact_mod_cast hM
  have hN : (M:ℝ) ≤ N := by exact_mod_cast hMN
  have hpack' : (J:ℝ)*((M:ℝ)*(M-1)) ≤ (N:ℝ)^2 := by
    have H := (Nat.cast_le (α := ℝ)).mpr hpack
    push_cast [Nat.cast_sub (show 1 ≤ M by omega)] at H
    exact H
  let r := Real.sqrt ((N:ℝ)/M)
  have hr : 1 ≤ r := by
    apply (Real.le_sqrt (by norm_num) (by positivity)).mpr
    simpa using (le_div_iff₀ hMp).mpr (by simpa using hN)
  have hrsq : r^2 = (N:ℝ)/M := Real.sq_sqrt (by positivity)
  have hrN : r^2*M = N := by rw [hrsq, div_mul_cancel₀ _ (ne_of_gt hMp)]
  have hJM : (J:ℝ)*(M:ℝ)^2 ≤ 2*(N:ℝ)^2 := by
    nlinarith [mul_nonneg (show (0:ℝ) ≤ J by positivity) (show (0:ℝ) ≤ M*(M-2) by positivity)]
  have hJ : (J:ℝ) ≤ 2*r^4 := by
    apply (mul_le_mul_iff_right₀ (sq_pos_of_pos hMp)).mp
    nlinarith [sq_nonneg (r^2*M-(N:ℝ)), sq_nonneg (r^2*M+(N:ℝ))]
  have hre : r ≤ Real.exp r := by linarith [Real.add_one_le_exp r]
  have hre4 : r^4 ≤ Real.exp (4*r) := by
    rw [show (4:ℝ)*r = (4:ℕ)*r by norm_num, Real.exp_nat_mul]
    exact pow_le_pow_left₀ (by positivity) hre 4
  have hsmall : Real.exp (-2) < (1/4:ℝ) := by
    have he : (2:ℝ) < Real.exp 1 := by simpa only [one_add_one_eq_two] using Real.add_one_lt_exp (by norm_num : (1:ℝ) ≠ 0)
    have he2 : (4:ℝ) < Real.exp 2 := by
      calc
        (4:ℝ) < (Real.exp 1)^2 := by nlinarith [Real.exp_pos (1:ℝ)]
        _ = Real.exp 2 := by rw [← Real.exp_nat_mul]; norm_num
    rw [Real.exp_neg]
    rw [← one_div]
    exact (div_lt_div_iff_of_pos_left (by norm_num) (Real.exp_pos _) (by norm_num)).mpr he2
  calc
    (J:ℝ)*Real.exp (-(256/3:ℝ)*r) ≤ 2*r^4*Real.exp (-(256/3:ℝ)*r) :=
      mul_le_mul_of_nonneg_right hJ (Real.exp_pos _).le
    _ ≤ 2*Real.exp (4*r)*Real.exp (-(256/3:ℝ)*r) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hre4 (by norm_num)) (Real.exp_pos _).le
    _ = 2*Real.exp (4*r-(256/3:ℝ)*r) := by rw [mul_assoc, ← Real.exp_add]; congr 2; ring
    _ ≤ 2*Real.exp (-2) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply Real.exp_le_exp.mpr
      linarith
    _ < 1/2 := by linarith
end SharpRamseyFive.RichParameters

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_Center
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

open scoped BigOperators

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal

namespace SharpRamseyFive.ProjectiveReduction
open Module Submodule
open scoped BigOperators

variable {K V : Type*} [Field K] [Infinite K] [AddCommGroup V] [Module K V]

theorem exists_center {ι : Type*} [Finite ι] (W : ι → Submodule K V)
    (hW : ∀ i, W i ≠ ⊤) : ∃ v : V, ∀ i, v ∉ W i :=
  Submodule.exists_forall_notMem_of_forall_ne_top W hW

omit [Infinite K] in

theorem quotient_injOn {W : Submodule K V} {v : V} (hv : v ∉ W) :
    Set.InjOn (Submodule.mkQ (K ∙ v)) W := by
  intro x hx y hy hxy
  have hmem : x - y ∈ K ∙ v := by
    exact (Submodule.Quotient.eq (K ∙ v)).mp hxy
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hmem
  have haw : a • v ∈ W := ha ▸ W.sub_mem hx hy
  have ha0 : a = 0 := by
    by_contra ha0
    exact hv ((W.smul_mem_iff ha0).mp haw)
  simpa [ha0, eq_comm, sub_eq_zero] using ha

theorem exists_projection [FiniteDimensional K V] {ι : Type*} [Finite ι]
    [Nonempty ι] (n : ℕ) (hdim : finrank K V = n + 1)
    (W : ι → Submodule K V) (hW : ∀ i, W i ≠ ⊤) :
    ∃ f : V →ₗ[K] (Fin n → K), Function.Surjective f ∧
      ∀ i, Set.InjOn f (W i) := by
  classical
  obtain ⟨v, hv⟩ := exists_center W hW
  have hv0 : v ≠ 0 := by
    intro he
    exact hv (Classical.arbitrary ι) (he ▸ (W _).zero_mem)
  have hr : finrank K (V ⧸ (K ∙ v)) = n := by
    have he := Submodule.finrank_quotient_add_finrank (K ∙ v)
    rw [finrank_span_singleton hv0, hdim] at he
    omega
  let e : (V ⧸ (K ∙ v)) ≃ₗ[K] (Fin n → K) :=
    LinearEquiv.ofFinrankEq _ _ (by simpa using hr)
  refine ⟨e.toLinearMap.comp (Submodule.mkQ (K ∙ v)), ?_, ?_⟩
  · exact e.surjective.comp (Submodule.mkQ_surjective _)
  · intro i x hx y hy hxy
    exact quotient_injOn (hv i) hx hy (e.injective hxy)

theorem exists_projection_preserving_spans [FiniteDimensional K V]
    (n : ℕ) (hdim : finrank K V = n + 1) (X : Finset V) :
    ∃ f : V →ₗ[K] (Fin n → K), Function.Surjective f ∧
      ∀ Y : Finset V, Y ⊆ X → Submodule.span K (Y : Set V) ≠ ⊤ →
        Set.InjOn f (Submodule.span K (Y : Set V)) := by
  classical
  let I := {Y : Finset V // Y ∈ X.powerset}
  let : Nonempty I := ⟨⟨∅, by simp⟩⟩
  have hb : (⊥ : Submodule K V) ≠ ⊤ := by
    intro he
    have hr := congrArg (fun W : Submodule K V => finrank K W) he
    simp [hdim] at hr
  let W : I → Submodule K V := fun Y =>
    if Submodule.span K (Y.val : Set V) = ⊤ then ⊥ else
      Submodule.span K (Y.val : Set V)
  have hW : ∀ i, W i ≠ ⊤ := by
    intro i
    dsimp [W]
    split_ifs with hi
    · exact hb
    · exact hi
  obtain ⟨f, hf, hfi⟩ := exists_projection n hdim W hW
  refine ⟨f, hf, ?_⟩
  intro Y hY hY'
  have H := hfi ⟨Y, Finset.mem_powerset.mpr hY⟩
  simpa [W, hY'] using H

omit [Infinite K] in

theorem finrank_map_of_injOn {U : Type*} [AddCommGroup U] [Module K U]
    (f : V →ₗ[K] U) (W : Submodule K V) (hf : Set.InjOn f W) :
    finrank K (W.map f) = finrank K W := by
  have hi : Function.Injective (f.comp W.subtype) := by
    intro x y hxy
    exact Subtype.ext (hf x.property y.property hxy)
  have hr := LinearMap.finrank_range_of_inj hi
  have he : (f.comp W.subtype).range = W.map f := by
    ext y
    simp [LinearMap.mem_range, Submodule.mem_map]
  rwa [he] at hr

end SharpRamseyFive.ProjectiveReduction

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_SplitEquiv
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open scoped BigOperators
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal
namespace SharpRamseyFive.AffineChart
open Module
open scoped LinearAlgebra.Projectivization
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem exists_coordinates_of_vectors [Infinite K] [FiniteDimensional K V]
    {ι : Type*} [Finite ι] [Nonempty ι] (n : ℕ) (hdim : finrank K V = n+1)
    (v : ι → V) (hv : ∀ i, v i ≠ 0) :
    ∃ e : V ≃ₗ[K] K × (Fin n → K), ∀ i, (e (v i)).1 ≠ 0 := by
  obtain ⟨φ, hφ⟩ := Module.exists_dual_forall_apply_ne_zero (K := K) v hv
  have hφ0 : φ ≠ 0 := by
    intro h
    exact hφ (Classical.arbitrary ι) (by simp [h])
  obtain ⟨o, ho⟩ := LinearMap.surjective hφ0 1
  have hk : finrank K (LinearMap.ker φ) = n := by
    have h := Module.Dual.finrank_ker_add_one_of_ne_zero hφ0
    omega
  let c : LinearMap.ker φ ≃ₗ[K] (Fin n → K) :=
    LinearEquiv.ofFinrankEq _ _ (by simpa using hk)
  exact ⟨(splitEquiv φ o ho).trans ((LinearEquiv.refl K K).prodCongr c), hφ⟩

variable {U : Type*} [AddCommGroup U] [Module K U]

lemma lift_normalize (v : K × U) (hv : v.1 ≠ 0) :
    (1, normalize v) = v.1⁻¹ • v := by
  ext <;> simp [normalize, hv]

lemma reconstruct (v : K × U) (hv : v.1 ≠ 0) :
    v.1 • (1, normalize v) = v := by
  rw [lift_normalize v hv, smul_smul, mul_inv_cancel₀ hv, one_smul]

end SharpRamseyFive.AffineChart

namespace SharpRamseyFive.ProjectiveReduction
open Module Submodule
variable {K V : Type*} [Field K] [Infinite K] [AddCommGroup V] [Module K V]

theorem exists_projection_preserving_ranks [FiniteDimensional K V]
    (n : ℕ) (hdim : finrank K V = n + 1) (X : Finset V) :
    ∃ f : V →ₗ[K] (Fin n → K), Function.Surjective f ∧
      ∀ Y : Finset V, Y ⊆ X →
        finrank K (Submodule.span K (f '' (Y : Set V))) =
          min (finrank K (Submodule.span K (Y : Set V))) n := by
  obtain ⟨f, hf, hfi⟩ := exists_projection_preserving_spans n hdim X
  refine ⟨f, hf, ?_⟩
  intro Y hY
  rw [Submodule.span_image]
  by_cases he : Submodule.span K (Y : Set V) = ⊤
  · rw [he, Submodule.map_top, LinearMap.range_eq_top.mpr hf]
    simp [hdim]
  · rw [finrank_map_of_injOn f _ (hfi Y hY he)]
    have hr := Submodule.finrank_lt he
    rw [hdim] at hr
    exact (min_eq_left (by omega)).symm
end SharpRamseyFive.ProjectiveReduction

namespace SharpRamseyFive.ScalarExtension
open Module
variable {K L I : Type*} [Field K] [Field L] [Algebra K L]

lemma coordinateMap_mem_span {s : Set (I → K)} {v : I → K}
    (hv : v ∈ Submodule.span K s) :
    coordinateMap (L := L) v ∈ Submodule.span L (coordinateMap '' s) := by
  induction hv using Submodule.span_induction with
  | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
  | zero => simp
  | add x y hx hy ihx ihy => simpa using Submodule.add_mem _ ihx ihy
  | smul a x hx ih =>
    simpa using Submodule.smul_mem
      (Submodule.span L (coordinateMap '' s)) (algebraMap K L a) ih

theorem finrank_span_range [Finite I] {J : Type*} (v : J → I → K) :
    finrank L (Submodule.span L (Set.range (coordinateMap (L := L) ∘ v))) =
      finrank K (Submodule.span K (Set.range v)) := by
  classical
  obtain ⟨B, a, _, hspan, hi⟩ := exists_linearIndependent' K v
  let := hi.finite
  let : Fintype B := Fintype.ofFinite B
  have hiL : LinearIndependent L (coordinateMap (L := L) ∘ (v ∘ a)) :=
    linearIndependent_algebraMap_comp_iff.mpr hi
  have he : Submodule.span L (Set.range (coordinateMap (L := L) ∘ (v ∘ a))) =
      Submodule.span L (Set.range (coordinateMap (L := L) ∘ v)) := by
    apply le_antisymm
    · apply Submodule.span_mono
      rintro _ ⟨b, rfl⟩
      exact ⟨a b, rfl⟩
    · apply Submodule.span_le.mpr
      rintro _ ⟨i, rfl⟩
      have hm : v i ∈ Submodule.span K (Set.range (v ∘ a)) := by
        rw [hspan]
        exact Submodule.subset_span ⟨i, rfl⟩
      have H := coordinateMap_mem_span (L := L) hm
      simpa [← Set.range_comp, Function.comp_assoc] using H
  rw [← he, finrank_span_eq_card hiL, ← hspan, finrank_span_eq_card hi]
end SharpRamseyFive.ScalarExtension

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_FinrankSpanImage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open scoped BigOperators
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal
namespace SharpRamseyFive.ScalarExtension
open Module
variable {K L I : Type*} [Field K] [Field L] [Algebra K L]

theorem finrank_span_image [Finite I] (s : Set (I → K)) :
    finrank L (Submodule.span L (coordinateMap (L := L) '' s)) =
      finrank K (Submodule.span K s) := by
  have h := finrank_span_range (L := L) (fun v : s => v.val)
  rw [Set.range_comp, Subtype.range_val] at h
  exact h
end SharpRamseyFive.ScalarExtension

namespace SharpRamseyFive.AffineChart
open Module
variable {K U V : Type*} [Field K] [AddCommGroup U] [Module K U]
    [AddCommGroup V] [Module K V]

lemma span_lift_normalize {ι : Type*} (v : ι → K × U) (hv : ∀ i, (v i).1 ≠ 0) :
    Submodule.span K (Set.range (fun i => ((1 : K), normalize (v i)))) =
      Submodule.span K (Set.range v) := by
  apply le_antisymm <;> apply Submodule.span_le.mpr
  · rintro _ ⟨i, rfl⟩
    change ((1 : K), normalize (v i)) ∈ _
    rw [lift_normalize _ (hv i)]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  · rintro _ ⟨i, rfl⟩
    rw [← reconstruct _ (hv i)]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

lemma finrank_lift_normalize {ι : Type*} (e : V ≃ₗ[K] K × U)
    (v : ι → V) (hv : ∀ i, (e (v i)).1 ≠ 0) :
    finrank K (Submodule.span K (Set.range (fun i => ((1 : K), normalize (e (v i)))))) =
      finrank K (Submodule.span K (Set.range v)) := by
  rw [span_lift_normalize _ hv]
  change finrank K (Submodule.span K (Set.range (e.toLinearMap ∘ v))) = _
  rw [Set.range_comp, Submodule.span_image, LinearEquiv.finrank_map_eq]

lemma lift_mem_span_pair (x y z : U) :
    ((1 : K), z) ∈ Submodule.span K {((1 : K), x), ((1 : K), y)} ↔
      ∃ a : K, x + a • (y - x) = z := by
  rw [Submodule.mem_span_pair]
  constructor
  · rintro ⟨a, b, h⟩
    have h1 : a + b = 1 := by simpa using congrArg Prod.fst h
    have h2 : a • x + b • y = z := congrArg Prod.snd h
    refine ⟨b, ?_⟩
    rw [← h2, smul_sub, show a = 1-b by linear_combination h1]
    simp only [sub_smul, one_smul]
    abel
  · rintro ⟨a, rfl⟩
    refine ⟨1-a, a, ?_⟩
    ext
    · simp
    · change (1-a) • x + a • y = x + a • (y-x)
      simp only [sub_smul, one_smul, smul_sub]
      abel
end SharpRamseyFive.AffineChart

namespace SharpRamseyFive.ProjectiveReduction
open Module Submodule
variable {K V : Type*} [Field K] [Infinite K] [AddCommGroup V] [Module K V]

theorem exists_to_four [FiniteDimensional K V]
    (hdim : finrank K V = 4 ∨ finrank K V = 5) (X : Finset V) :
    ∃ f : V →ₗ[K] (Fin 4 → K), Function.Surjective f ∧
      ∀ Y : Finset V, Y ⊆ X →
        finrank K (Submodule.span K (f '' (Y : Set V))) =
          min (finrank K (Submodule.span K (Y : Set V))) 4 := by
  rcases hdim with hd | hd
  · let e : V ≃ₗ[K] (Fin 4 → K) := LinearEquiv.ofFinrankEq _ _ (by simpa using hd)
    refine ⟨e.toLinearMap, e.surjective, ?_⟩
    intro Y _
    rw [Submodule.span_image, LinearEquiv.finrank_map_eq]
    exact (min_eq_left (by simpa [hd] using (Submodule.span K (Y : Set V)).finrank_le)).symm
  · exact exists_projection_preserving_ranks 4 hd X

omit [Infinite K] in
lemma nonzero_of_rank_preserved {U : Type*} [AddCommGroup U] [Module K U]
    (f : V →ₗ[K] U) (X : Finset V) (hf : ∀ Y : Finset V, Y ⊆ X →
      finrank K (Submodule.span K (f '' (Y : Set V))) =
        min (finrank K (Submodule.span K (Y : Set V))) 4)
    {v : V} (hv : v ∈ X) (hv0 : v ≠ 0) : f v ≠ 0 := by
  classical
  have h := hf {v} (by simpa)
  rw [Finset.coe_singleton, Set.image_singleton] at h
  rw [finrank_span_singleton hv0] at h
  intro h0
  rw [Submodule.span_singleton_eq_bot.mpr h0] at h
  simp at h
end SharpRamseyFive.ProjectiveReduction

namespace SharpRamseyFive.AffineRealization
open Module
open AffineChart ScalarExtension ProjectiveReduction
variable {K L I ι : Type*} [Field K] [Field L] [Algebra K L] [Infinite L]
    [Fintype I] [Fintype ι] [Nonempty ι]

theorem exists_realization (hI : Fintype.card I = 4 ∨ Fintype.card I = 5)
    (v : ι → I → K) (hv : ∀ i, v i ≠ 0) :
    ∃ a : ι → Fin 3 → L, ∀ Y : Finset ι,
      finrank L (Submodule.span L ((fun i => ((1 : L), a i)) '' (Y : Set ι))) =
        min (finrank K (Submodule.span K (v '' (Y : Set ι)))) 4 := by
  classical
  let w : ι → I → L := coordinateMap ∘ v
  let X : Finset (I → L) := Finset.univ.image w
  obtain ⟨f, _, hr⟩ := exists_to_four (K := L)
    (V := I → L) (by simpa using hI) X
  have hw (i : ι) : f (w i) ≠ 0 :=
    nonzero_of_rank_preserved f X hr (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)
      (coordinateMap_ne_zero _ (hv i))
  obtain ⟨e, he⟩ := exists_coordinates_of_vectors (K := L) 3 (by simp)
    (fun i => f (w i)) hw
  refine ⟨fun i => normalize (e (f (w i))), ?_⟩
  intro Y
  have hnorm := finrank_lift_normalize e (fun i : Y => f (w i.val)) (fun i => he i.val)
  have hrY := hr (Y.image w) (Finset.image_subset_image (Finset.subset_univ Y))
  have hscalar := finrank_span_image (L := L) (v '' (Y : Set ι))
  have hn : Set.range (fun i : Y => f (w i.val)) = f '' (w '' (Y : Set ι)) := by
    ext z
    simp
  have hn' : Set.range (fun i : Y => ((1 : L), normalize (e (f (w i.val))))) =
      (fun i => ((1 : L), normalize (e (f (w i))))) '' (Y : Set ι) := by
    ext z
    simp
  rw [hn, hn'] at hnorm
  rw [Finset.coe_image] at hrY
  rw [hnorm, hrY]
  congr 1
  rw [Set.image_image] at hscalar
  exact hscalar
end SharpRamseyFive.AffineRealization

namespace SharpRamseyFive.SubspaceExtension
open Module
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V]

theorem exists_add_rank (W : Submodule K V) (k : ℕ)
    (hk : finrank K W + k ≤ finrank K V) :
    ∃ U : Submodule K V, W ≤ U ∧ finrank K U = finrank K W + k := by
  induction k with
  | zero => exact ⟨W, le_rfl, by simp⟩
  | succ k ih =>
    obtain ⟨U, hWU, hU⟩ := ih (by omega)
    have hUt : U ≠ ⊤ := by
      intro he
      rw [he, finrank_top] at hU
      omega
    have hx : ∃ x : V, x ∉ U := by
      by_contra! h
      apply hUt
      ext x
      simp [h]
    obtain ⟨x, hx⟩ := hx
    refine ⟨U ⊔ K ∙ x, hWU.trans le_sup_left, ?_⟩
    rw [Submodule.finrank_sup_span_singleton hx, hU]
    omega

theorem exists_rank (W : Submodule K V) (n : ℕ)
    (hW : finrank K W ≤ n) (hn : n ≤ finrank K V) :
    ∃ U : Submodule K V, W ≤ U ∧ finrank K U = n := by
  obtain ⟨U, hU, hr⟩ := exists_add_rank W (n - finrank K W) (by omega)
  exact ⟨U, hU, by omega⟩
end SharpRamseyFive.SubspaceExtension

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_LinearForm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open scoped BigOperators
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal
namespace SharpRamseyFive.LinearPolynomial
open scoped BigOperators
open MvPolynomial Module
variable {K I : Type*} [Field K]

theorem exists_linear_form (P : MvPolynomial I K) (hP : P.totalDegree ≤ 1) :
    ∃ φ : (K × (I → K)) →ₗ[K] K, ∀ x, φ (1, x) = eval x P := by
  classical
  have hterm (d : P.support) :
      ∃ φ : (K × (I → K)) →ₗ[K] K,
        ∀ x, φ (1, x) = eval x (monomial d.val (P.coeff d.val)) := by
    have hd : d.val.degree ≤ 1 := (le_totalDegree d.property).trans hP
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hd with hd | hd
    · have he := (Finsupp.degree_eq_zero_iff _).mp hd
      refine ⟨P.coeff d.val • LinearMap.fst K K (I → K), ?_⟩
      intro x
      simp [he]
    · obtain ⟨i, hi⟩ := (Finsupp.sum_eq_one_iff d.val).mp hd
      refine ⟨P.coeff d.val • ((LinearMap.proj i).comp (LinearMap.snd K K (I → K))), ?_⟩
      intro x
      simp [hi, eval_monomial]
  choose φ hφ using hterm
  refine ⟨∑ d : P.support, φ d, ?_⟩
  intro x
  simp only [LinearMap.sum_apply]
  simp_rw [hφ]
  rw [← map_sum, Finset.sum_coe_sort P.support (fun d => monomial d (P.coeff d)), ← P.as_sum]

theorem exists_hyperplane [Infinite K] [Fintype I]
    (P : MvPolynomial I K) (hP : P.totalDegree = 1) :
    ∃ W : Submodule K (K × (I → K)), finrank K W = Fintype.card I ∧
      ∀ x, eval x P = 0 → ((1 : K), x) ∈ W := by
  obtain ⟨φ, hφ⟩ := exists_linear_form P hP.le
  have hφ0 : φ ≠ 0 := by
    intro he
    have hP0 : P = 0 := MvPolynomial.funext (fun x => by simpa [he] using (hφ x).symm)
    subst P
    simp at hP
  refine ⟨LinearMap.ker φ, ?_, ?_⟩
  · have h := Module.Dual.finrank_ker_add_one_of_ne_zero hφ0
    simp only [Module.finrank_prod, Module.finrank_self, Module.finrank_pi] at h
    omega
  · intro x hx
    rw [LinearMap.mem_ker, hφ, hx]
end SharpRamseyFive.LinearPolynomial

namespace SharpRamseyFive.AffineRealization

section
open Module
open scoped LinearAlgebra.Projectivization
variable {K L I ι : Type*} [Field K] [Field L] [Algebra K L]

lemma projective_pair_rank {V : Type*} [AddCommGroup V] [Module K V]
    {p r : ℙ K V} (hpr : p ≠ r) :
    finrank K (Submodule.span K {p.rep, r.rep}) = 2 := by
  have hi := Projectivization.independent_iff.mp
    ((Projectivization.independent_pair_iff_ne p r).mpr hpr)
  have hr : Set.range (Projectivization.rep ∘ ![p, r]) = {p.rep, r.rep} := by
    ext v
    simp only [Set.mem_range, Function.comp_apply, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp
    · rintro (rfl | rfl)
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
  have h := finrank_span_eq_card hi
  rw [hr] at h
  simpa using h

omit [Algebra K L] in

lemma injective_of_ranks [Fintype I] [DecidableEq ι]
    (p : ι → ℙ K (I → K)) (hp : Function.Injective p)
    (a : ι → Fin 3 → L)
    (hr : ∀ Y : Finset ι,
      finrank L (Submodule.span L ((fun i => ((1 : L), a i)) '' (Y : Set ι))) =
        min (finrank K (Submodule.span K ((fun i => (p i).rep) '' (Y : Set ι)))) 4) :
    Function.Injective a := by
  intro i j hij
  by_contra hn
  have h := hr {i,j}
  rw [Finset.coe_insert, Finset.coe_singleton, Set.image_pair, Set.image_pair, hij,
    Set.insert_eq_of_mem (Set.mem_singleton _), projective_pair_rank (by exact fun he => hn (hp he))] at h
  have hv : ((1 : L), a j) ≠ 0 := by
    intro he
    have he1 := congrArg Prod.fst he
    exact one_ne_zero he1
  rw [finrank_span_singleton hv] at h
  norm_num at h

theorem exists_projective_realization [Infinite L] [Fintype I] [Fintype ι] [Nonempty ι]
    (hI : Fintype.card I = 4 ∨ Fintype.card I = 5)
    (p : ι → ℙ K (I → K)) (hp : Function.Injective p) :
    ∃ a : ι → Fin 3 → L, Function.Injective a ∧ ∀ Y : Finset ι,
      finrank L (Submodule.span L ((fun i => ((1 : L), a i)) '' (Y : Set ι))) =
        min (finrank K (Submodule.span K ((fun i => (p i).rep) '' (Y : Set ι)))) 4 := by
  classical
  obtain ⟨a, ha⟩ := exists_realization (L := L) hI (fun i => (p i).rep)
    (fun i => (p i).rep_nonzero)
  exact ⟨a, injective_of_ranks p hp a ha, ha⟩
end

open Module MvPolynomial
open scoped LinearAlgebra.Projectivization Classical
variable {K L I ι : Type*} [Field K] [Field L] [Fintype I] [Fintype ι]

theorem plane_cap_of_ranks [Infinite L]
    (hI : 3 ≤ Fintype.card I) (p : ι → ℙ K (I → K))
    (a : ι → Fin 3 → L) (ha : Function.Injective a)
    (hr : ∀ Y : Finset ι,
      finrank L (Submodule.span L ((fun i => ((1 : L), a i)) '' (Y : Set ι))) =
        min (finrank K (Submodule.span K ((fun i => (p i).rep) '' (Y : Set ι)))) 4)
    (Kp : ℕ)
    (hcap : ∀ W : Submodule K (I → K), finrank K W = 3 →
      (Finset.univ.filter (fun i => (p i).rep ∈ W)).card ≤ Kp)
    (P : MvPolynomial (Fin 3) L) (hP : P.totalDegree = 1) :
    ((Finset.univ.image a).filter (fun y => eval y P = 0)).card ≤ Kp := by
  classical
  let Y : Finset ι := Finset.univ.filter (fun i => eval (a i) P = 0)
  obtain ⟨W, hW, hWmem⟩ := LinearPolynomial.exists_hyperplane P hP
  have hYW : Submodule.span L ((fun i => ((1 : L), a i)) '' (Y : Set ι)) ≤ W := by
    apply Submodule.span_le.mpr
    rintro z ⟨i, hi, rfl⟩
    exact hWmem _ (Finset.mem_filter.mp hi).2
  have hry : finrank K (Submodule.span K ((fun i => (p i).rep) '' (Y : Set ι))) ≤ 3 := by
    have hy := Submodule.finrank_mono hYW
    rw [hr Y, hW] at hy
    simp only [Fintype.card_fin] at hy
    omega
  obtain ⟨U, hU, hUrank⟩ := SubspaceExtension.exists_rank
    (Submodule.span K ((fun i => (p i).rep) '' (Y : Set ι))) 3 hry (by simpa using hI)
  have hYu : Y ⊆ Finset.univ.filter (fun i => (p i).rep ∈ U) := by
    intro i hi
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, hU ?_⟩
    exact Submodule.subset_span ⟨i, hi, rfl⟩
  have he : (Finset.univ.image a).filter (fun y => eval y P = 0) = Y.image a := by
    ext y
    simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and, Y]
    constructor
    · rintro ⟨⟨i, rfl⟩, hi⟩
      exact ⟨i, hi, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨⟨i, rfl⟩, hi⟩
  rw [he, Finset.card_image_of_injective _ ha]
  exact (Finset.card_le_card hYu).trans (hcap U hUrank)
end SharpRamseyFive.AffineRealization

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_MemPairRank
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open scoped BigOperators
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal
namespace SharpRamseyFive.SpanRank
open Module
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

lemma mem_pair_iff_rank [FiniteDimensional K V] (x y z : V)
    (hxy : finrank K (Submodule.span K {x,y}) = 2) :
    z ∈ Submodule.span K {x,y} ↔ finrank K (Submodule.span K {x,y,z}) ≤ 2 := by
  have hle : Submodule.span K {x,y} ≤ Submodule.span K {x,y,z} := by
    apply Submodule.span_mono
    intro w hw
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw ⊢
    tauto
  constructor
  · intro hz
    have he : Submodule.span K {x,y,z} ≤ Submodule.span K {x,y} := by
      apply Submodule.span_le.mpr
      intro w hw
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
      rcases hw with rfl | rfl | rfl
      · exact Submodule.subset_span (by simp)
      · exact Submodule.subset_span (by simp)
      · exact hz
    simpa only [hxy] using Submodule.finrank_mono he
  · intro hr
    have he := Submodule.eq_of_le_of_finrank_le hle (by simpa only [hxy] using hr)
    rw [he]
    exact Submodule.subset_span (by simp)
end SharpRamseyFive.SpanRank

namespace SharpRamseyFive.AffineRealization

section
open Module
open scoped LinearAlgebra.Projectivization Classical
variable {K L I ι : Type*} [Field K] [Field L] [Fintype I] [DecidableEq ι]

omit [DecidableEq ι] in
lemma span_pair_eq_line (p : ι → ℙ K (I → K)) (hp : Function.Injective p)
    (W : Submodule K (I → K)) (hW : finrank K W = 2)
    {i j : ι} (hij : i ≠ j) (hi : (p i).rep ∈ W) (hj : (p j).rep ∈ W) :
    Submodule.span K {(p i).rep, (p j).rep} = W := by
  apply Submodule.eq_of_le_of_finrank_eq
  · apply Submodule.span_le.mpr
    intro v hv
    rcases hv with rfl | hv
    · exact hi
    · exact (Set.mem_singleton_iff.mp hv) ▸ hj
  · rw [projective_pair_rank (fun he => hij (hp he)), hW]

theorem line_incidence_of_ranks
    (p : ι → ℙ K (I → K)) (hp : Function.Injective p)
    (a : ι → Fin 3 → L)
    (hr : ∀ Y : Finset ι,
      finrank L (Submodule.span L ((fun i => ((1 : L), a i)) '' (Y : Set ι))) =
        min (finrank K (Submodule.span K ((fun i => (p i).rep) '' (Y : Set ι)))) 4)
    (W : Submodule K (I → K)) (hW : finrank K W = 2)
    {i j : ι} (hij : i ≠ j) (hi : (p i).rep ∈ W) (hj : (p j).rep ∈ W) (k : ι) :
    (p k).rep ∈ W ↔ a k ∈ Set.range (fun t : L => a i + t • (a j-a i)) := by
  classical
  have hpij : p i ≠ p j := fun he => hij (hp he)
  have hpair : finrank L (Submodule.span L {((1 : L), a i), ((1 : L), a j)}) = 2 := by
    have h := hr {i,j}
    rw [Finset.coe_insert, Finset.coe_singleton, Set.image_pair, Set.image_pair,
      projective_pair_rank hpij] at h
    exact h
  have htriple := hr {i,j,k}
  rw [Finset.coe_insert, Finset.coe_insert, Finset.coe_singleton,
    Set.image_insert_eq, Set.image_pair, Set.image_insert_eq, Set.image_pair] at htriple
  rw [← span_pair_eq_line p hp W hW hij hi hj, SpanRank.mem_pair_iff_rank _ _ _ (projective_pair_rank hpij)]
  rw [Set.mem_range, ← AffineChart.lift_mem_span_pair, SpanRank.mem_pair_iff_rank _ _ _ hpair, htriple]
  omega

theorem distinct_lines_of_ranks {J : Type*}
    (p : ι → ℙ K (I → K)) (hp : Function.Injective p)
    (a : ι → Fin 3 → L)
    (hr : ∀ Y : Finset ι,
      finrank L (Submodule.span L ((fun i => ((1 : L), a i)) '' (Y : Set ι))) =
        min (finrank K (Submodule.span K ((fun i => (p i).rep) '' (Y : Set ι)))) 4)
    (W : J → Submodule K (I → K)) (hW : ∀ l, finrank K (W l) = 2)
    (hWinj : Function.Injective W) (i j : J → ι) (hij : ∀ l, i l ≠ j l)
    (hi : ∀ l, (p (i l)).rep ∈ W l) (hj : ∀ l, (p (j l)).rep ∈ W l) :
    Function.Injective (fun l => Set.range (fun t : L => a (i l)+t • (a (j l)-a (i l)))) := by
  intro l m hlm
  dsimp only at hlm
  apply hWinj
  apply Submodule.eq_of_le_of_finrank_eq
  · rw [← span_pair_eq_line p hp (W l) (hW l) (hij l) (hi l) (hj l)]
    apply Submodule.span_le.mpr
    intro z hz
    rcases hz with rfl | hz
    · apply (line_incidence_of_ranks p hp a hr (W m) (hW m) (hij m) (hi m) (hj m) _).mpr
      rw [← hlm]
      exact ⟨0, by simp⟩
    · rw [Set.mem_singleton_iff] at hz
      subst z
      apply (line_incidence_of_ranks p hp a hr (W m) (hW m) (hij m) (hi m) (hj m) _).mpr
      rw [← hlm]
      exact ⟨1, by simp⟩
  · rw [hW, hW]
end

open Module
open scoped LinearAlgebra.Projectivization Classical
variable {K L I ι : Type*} [Field K] [Field L] [Fintype I] [Fintype ι]

theorem line_count_of_ranks
    (p : ι → ℙ K (I → K)) (hp : Function.Injective p)
    (a : ι → Fin 3 → L) (ha : Function.Injective a)
    (hr : ∀ Y : Finset ι,
      finrank L (Submodule.span L ((fun i => ((1 : L), a i)) '' (Y : Set ι))) =
        min (finrank K (Submodule.span K ((fun i => (p i).rep) '' (Y : Set ι)))) 4)
    (W : Submodule K (I → K)) (hW : finrank K W = 2)
    {i j : ι} (hij : i ≠ j) (hi : (p i).rep ∈ W) (hj : (p j).rep ∈ W) :
    (Finset.univ.filter (fun k => (p k).rep ∈ W)).card =
      ((Finset.univ.image a).filter (fun y =>
        y ∈ Set.range (fun t : L => a i+t • (a j-a i)))).card := by
  classical
  apply Finset.card_bij (fun k _ => a k)
  · intro k hk
    refine Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩, ?_⟩
    exact (line_incidence_of_ranks p hp a hr W hW hij hi hj k).mp (Finset.mem_filter.mp hk).2
  · intro k hk l hl hkl
    exact ha hkl
  · intro y hy
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hy).1
    refine ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, rfl⟩
    exact (line_incidence_of_ranks p hp a hr W hW hij hi hj k).mpr (Finset.mem_filter.mp hy).2

omit [Fintype I] in

theorem exists_line_indices {J : Type*}
    (p : ι → ℙ K (I → K)) (W : J → Submodule K (I → K))
    (hM : ∀ l, 2 ≤ (Finset.univ.filter (fun k => (p k).rep ∈ W l)).card) :
    ∃ i j : J → ι, (∀ l, i l ≠ j l) ∧
      (∀ l, (p (i l)).rep ∈ W l) ∧ (∀ l, (p (j l)).rep ∈ W l) := by
  classical
  have H (l : J) := Finset.one_lt_card.mp (lt_of_lt_of_le (by decide : 1 < 2) (hM l))
  choose i hi j hj hij using H
  exact ⟨i, j, hij, fun l => (Finset.mem_filter.mp (hi l)).2,
    fun l => (Finset.mem_filter.mp (hj l)).2⟩

end SharpRamseyFive.AffineRealization

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_ProjectiveLinePairPacking
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open scoped BigOperators
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal
namespace SharpRamseyFive.AffineRealization
open Module
open scoped LinearAlgebra.Projectivization Classical
variable {K I ι J : Type*} [Field K] [Fintype I] [Fintype ι] [Fintype J]

theorem projective_line_pair_packing
    (p : ι → ℙ K (I → K)) (hp : Function.Injective p)
    (W : J → Submodule K (I → K)) (hW : ∀ l, finrank K (W l) = 2)
    (hWinj : Function.Injective W) (M : ℕ)
    (hM : ∀ l, M ≤ (Finset.univ.filter (fun k => (p k).rep ∈ W l)).card) :
    Fintype.card J * (M * (M-1)) ≤ (Fintype.card ι)^2 := by
  classical
  let A (l : J) : Finset ι := Finset.univ.filter (fun k => (p k).rep ∈ W l)
  have hd : (↑(Finset.univ : Finset J) : Set J).PairwiseDisjoint (fun l => (A l).offDiag) := by
    intro l hl m hm hlm
    apply Finset.disjoint_left.mpr
    intro z hz hz'
    obtain ⟨hi, hj, hij⟩ := Finset.mem_offDiag.mp hz
    obtain ⟨hi', hj', _⟩ := Finset.mem_offDiag.mp hz'
    apply hlm
    apply hWinj
    rw [← span_pair_eq_line p hp _ (hW l) hij (Finset.mem_filter.mp hi).2
        (Finset.mem_filter.mp hj).2,
      ← span_pair_eq_line p hp _ (hW m) hij (Finset.mem_filter.mp hi').2
        (Finset.mem_filter.mp hj').2]
  calc
    Fintype.card J * (M * (M-1)) = ∑ _l : J, M * (M-1) := by simp
    _ ≤ ∑ l : J, (A l).offDiag.card := by
      apply Finset.sum_le_sum
      intro l hl
      rw [Finset.offDiag_card]
      have he (n : ℕ) : n*n-n = n*(n-1) := by rw [Nat.mul_sub_left_distrib, mul_one]
      rw [he]
      exact Nat.mul_le_mul (hM l) (Nat.sub_le_sub_right (hM l) 1)
    _ = (Finset.univ.biUnion (fun l => (A l).offDiag)).card := (Finset.card_biUnion hd).symm
    _ ≤ Fintype.card (ι × ι) := Finset.card_le_univ _
    _ = (Fintype.card ι)^2 := by simp [pow_two]
end SharpRamseyFive.AffineRealization

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Probability_SamplingDegree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open scoped BigOperators
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal
namespace SharpRamseyFive.RichParameters
open scoped Real

lemma exists_sampling_degree (N M q : ℕ) (hM : 0 < M) (hNM : M ≤ N)
    (hlarge : (1024 : ℝ)^2 * N ≤ (M : ℝ)^3)
    (hq : 51 * Real.sqrt ((N : ℝ) / M) < q) :
    ∃ (p : ℝ) (h : ℕ),
      0 < p ∧ p ≤ 1 ∧
      2*p*N < ((h+1)^3 : ℕ) ∧ (3*h : ℕ) ≤ p*M/2 ∧
      3*h < q ∧ 18*h < M ∧ h^2*M ≤ 289*N ∧
      p*M = 1024*Real.sqrt ((N : ℝ)/M) := by
  let r := Real.sqrt ((N : ℝ)/M)
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hM
  have hMnz : (M : ℝ) ≠ 0 := ne_of_gt hMpos
  have hNM' : (M : ℝ) ≤ N := by exact_mod_cast hNM
  have hr1 : 1 ≤ r := by
    apply (Real.le_sqrt (by norm_num) (by positivity)).mpr
    simpa using (le_div_iff₀ hMpos).mpr (by simpa using hNM')
  have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hr1
  have hrsq : r^2 = (N : ℝ)/M := Real.sq_sqrt (by positivity)
  have hrN : r^2*M = N := by rw [hrsq, div_mul_cancel₀ _ hMnz]
  have hrM : 1024*r ≤ M := by
    have hh : (1024*r)^2 ≤ (M : ℝ)^2 := by
      apply (mul_le_mul_iff_left₀ hMpos).mp
      nlinarith [hrN]
    nlinarith [sq_nonneg (1024*r-M)]
  let h : ℕ := ⌈16*r⌉₊
  have hhlo : 16*r ≤ (h : ℝ) := Nat.le_ceil _
  have hhhi : (h : ℝ) < 16*r+1 := Nat.ceil_lt_add_one (by positivity)
  have hh17 : (h : ℝ) < 17*r := by linarith
  refine ⟨1024*r/M, h, by positivity, (div_le_one hMpos).mpr hrM, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hN : (N : ℝ) = r^2*M := hrN.symm
    rw [hN]
    have he : 2*(1024*r/M)*(r^2*M) = 2048*r^3 := by field_simp; ring
    rw [he]
    have hr3 : 0 < r^3 := pow_pos hrpos _
    have hpow := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ 16*r) hhlo 3
    push_cast
    nlinarith [hpow, pow_nonneg (show (0:ℝ) ≤ h by positivity) 2]
  · push_cast
    have he : (1024*r/M)*M = 1024*r := div_mul_cancel₀ _ hMnz
    rw [he]
    linarith
  · apply (Nat.cast_lt (α := ℝ)).mp
    push_cast
    dsimp [r] at hh17 ⊢
    linarith
  · apply (Nat.cast_lt (α := ℝ)).mp
    push_cast
    linarith
  · apply (Nat.cast_le (α := ℝ)).mp
    push_cast
    have hhsq : (h : ℝ)^2 ≤ (17*r)^2 := pow_le_pow_left₀ (by positivity) hh17.le 2
    have H := mul_le_mul_of_nonneg_right hhsq hMpos.le
    nlinarith [hrN]
  · exact div_mul_cancel₀ _ hMnz
end SharpRamseyFive.RichParameters

end OAI
end

section
-- module Solutions.OAIQ060_R5.SharpRamsey_Geometry_RichLines
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Incidence bounds for rich lines and finite point configurations. -/

section
section

section

namespace SharpLogRamsey.ImplicitBranch
open Polynomial
open scoped Ring

/-
Copyright (c) 2021 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin

The following Hensel lifting theorem is adapted from Mathlib.RingTheory.Henselian.
Source: https://github.com/leanprover-community/mathlib4/blob/d13f23b723b8a846827a245b89c10fc7d3f11612/Mathlib/RingTheory/Henselian.lean

This code has been modified.
-/

 theorem hensel_nonmonic {R : Type*} [CommRing R] (I : Ideal R)
    [IsAdicComplete I R] (f : Polynomial R) (a₀ : R)
    (h₁ : f.eval a₀ ∈ I)
    (h₂ : IsUnit (Ideal.Quotient.mk I (f.derivative.eval a₀))) :
    ∃ a, f.IsRoot a ∧ a-a₀ ∈ I := by
  classical
    let f' := derivative f

    let c : ℕ → R := fun n => Nat.recOn n a₀ fun _ b => b - f.eval b * (f'.eval b)⁻¹ʳ
    have hc : ∀ n, c (n + 1) = c n - f.eval (c n) * (f'.eval (c n))⁻¹ʳ := by
      intro n
      simp only [c]

    have hc_mod : ∀ n, c n ≡ a₀ [SMOD I] := by
      intro n
      induction n with
      | zero => rfl
      | succ n ih => ?_
      rw [hc, sub_eq_add_neg, ← add_zero a₀]
      refine ih.add ?_
      rw [SModEq.zero, Ideal.neg_mem_iff]
      refine I.mul_mem_right _ ?_
      rw [← SModEq.zero] at h₁ ⊢
      exact (ih.eval f).trans h₁
    have hf'c : ∀ n, IsUnit (f'.eval (c n)) := by
      intro n
      have := isLocalHom_of_le_jacobson_bot I (IsAdicComplete.le_jacobson_bot I)
      apply IsUnit.of_map (Ideal.Quotient.mk I)
      convert! h₂ using 1
      all_goals try with_reducible_and_instances rfl
      exact SModEq.def.mp ((hc_mod n).eval _)
    have hfcI : ∀ n, f.eval (c n) ∈ I ^ (n + 1) := by
      intro n
      induction n with
      | zero => simpa only [Nat.rec_zero, zero_add, pow_one] using! h₁
      | succ n ih => ?_
      rw [← taylor_eval_sub (c n), hc, sub_eq_add_neg, sub_eq_add_neg,
        add_neg_cancel_comm]
      rw [eval_eq_sum, sum_over_range' _ _ _ (lt_add_of_pos_right _ zero_lt_two), ←
        Finset.sum_range_add_sum_Ico _ (Nat.le_add_left _ _)]
      swap
      · intro i
        rw [zero_mul]
      refine Ideal.add_mem _ ?_ ?_
      · rw [← one_add_one_eq_two, Finset.sum_range_succ, Finset.range_one, Finset.sum_singleton,
          taylor_coeff_zero, taylor_coeff_one, pow_zero, pow_one, mul_one, mul_neg,
          mul_left_comm, Ring.mul_inverse_cancel _ (hf'c n), mul_one, add_neg_cancel]
        exact Ideal.zero_mem _
      · refine Submodule.sum_mem _ ?_
        simp only [Finset.mem_Ico]
        rintro i ⟨h2i, _⟩
        have aux : n + 2 ≤ i * (n + 1) := by trans 2 * (n + 1) <;> nlinarith only [h2i]
        refine Ideal.mul_mem_left _ _ (Ideal.pow_le_pow_right aux ?_)
        rw [pow_mul']
        exact Ideal.pow_mem_pow ((Ideal.neg_mem_iff _).2 <| Ideal.mul_mem_right _ _ ih) _

    have aux : ∀ m n, m ≤ n → c m ≡ c n [SMOD (I ^ m • ⊤ : Ideal R)] := by
      intro m n hmn
      rw [← Ideal.one_eq_top, Ideal.smul_eq_mul, mul_one]
      obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
      clear hmn
      induction k with
      | zero => rw [add_zero]
      | succ k ih => ?_
      rw [← add_assoc, hc, ← add_zero (c m), sub_eq_add_neg]
      refine ih.add ?_
      symm
      rw [SModEq.zero, Ideal.neg_mem_iff]
      refine Ideal.mul_mem_right _ _ (Ideal.pow_le_pow_right ?_ (hfcI _))
      rw [add_assoc]
      exact le_self_add

    obtain ⟨a, ha⟩ := IsPrecomplete.prec' c (aux _ _)
    refine ⟨a, ?_, ?_⟩
    · show f.IsRoot a
      suffices ∀ n, f.eval a ≡ 0 [SMOD (I ^ n • ⊤ : Ideal R)] by exact IsHausdorff.haus' _ this
      intro n
      specialize ha n
      rw [← Ideal.one_eq_top, Ideal.smul_eq_mul, mul_one] at ha ⊢
      refine (ha.symm.eval f).trans ?_
      rw [SModEq.zero]
      exact Ideal.pow_le_pow_right le_self_add (hfcI _)
    · show a - a₀ ∈ I
      specialize ha (0 + 1)
      rw [hc, pow_one, ← Ideal.one_eq_top, Ideal.smul_eq_mul, mul_one, sub_eq_add_neg] at ha
      rw [← SModEq.sub_mem, ← add_zero a₀]
      refine ha.symm.trans (SModEq.rfl.add ?_)
      rw [SModEq.zero, Ideal.neg_mem_iff]
      exact Ideal.mul_mem_right _ _ h₁

variable {σ K R S : Type*} [Fintype σ] [DecidableEq σ] [Field K]
  [CommRing R] [CommRing S] [Algebra K R] [Algebra K S]

lemma aeval_hom {τ : Type*} (φ : R →ₐ[K] S) (x : τ → R) (F : MvPolynomial τ K) :
    φ (MvPolynomial.aeval x F) = MvPolynomial.aeval (fun i => φ (x i)) F := by
  induction F using MvPolynomial.induction_on with
  | C c => simp
  | add f g hf hg => simp [hf,hg]
  | mul_X f i hf => simp [hf]

omit [Fintype σ] [DecidableEq σ] in

lemma eval_liftZ (F : MvPolynomial (Option σ) K) (h : MvPowerSeries σ K) :
    (liftZ F).eval h = MvPolynomial.aeval (fun o => o.elim h MvPowerSeries.X) F := by
  induction F using MvPolynomial.induction_on with
  | C c => simp [liftZ,Polynomial.algebraMap_apply]
  | add f g hf hg => simp_all [liftZ]
  | mul_X f i hf => cases i <;> simp_all [liftZ]
omit [Fintype σ] in

lemma derivative_liftZ (F : MvPolynomial (Option σ) K) :
    (liftZ F).derivative = liftZ (MvPolynomial.pderiv none F) := by
  induction F using MvPolynomial.induction_on with
  | C c => simp [liftZ,Polynomial.algebraMap_apply]
  | add f g hf hg => simp_all [liftZ]
  | mul_X f i hf =>
    cases i <;> simp_all [liftZ,Derivation.leibniz,smul_eq_mul,
      MvPolynomial.pderiv_X] <;> ring
omit [Fintype σ] [DecidableEq σ] in

lemma zeroCoeff_aeval (F : MvPolynomial (Option σ) K) :
    MvPowerSeries.constantCoeff
      (MvPolynomial.aeval (fun o => o.elim 0 MvPowerSeries.X) F) =
      MvPolynomial.constantCoeff F := by
  let φ : MvPowerSeries σ K →ₐ[K] K :=
    { MvPowerSeries.constantCoeff with
      commutes' := by intro c; simp [← MvPowerSeries.c_eq_algebraMap] }
  have H := aeval_hom φ (fun o => o.elim 0 MvPowerSeries.X) F
  have hz : (fun o : Option σ => φ (o.elim 0 MvPowerSeries.X)) = 0 := by
    funext o
    cases o with
    | none => exact map_zero φ
    | some i => change MvPowerSeries.constantCoeff (MvPowerSeries.X i) = 0; simp
  rw [hz,MvPolynomial.aeval_zero] at H
  exact H

theorem exists_formal_branch (F : MvPolynomial (Option σ) K)
    (hF : MvPolynomial.constantCoeff F = 0)
    (hD : MvPolynomial.constantCoeff (MvPolynomial.pderiv none F) ≠ 0) :
    ∃ h : MvPowerSeries σ K,
      MvPowerSeries.constantCoeff h = 0 ∧
      MvPolynomial.aeval (fun o => o.elim h MvPowerSeries.X) F = 0 := by
  let I : Ideal (MvPowerSeries σ K) := Ideal.span (Set.range MvPowerSeries.X)
  have hmem : (liftZ F).eval 0 ∈ I := by
    rw [← Ideal.Quotient.eq_zero_iff_mem,eval_liftZ]
    let φ : MvPowerSeries σ K →ₐ[K] MvPowerSeries σ K ⧸ I := Ideal.Quotient.mkₐ K I
    change φ _ = 0
    rw [aeval_hom]
    have hz : (fun o : Option σ => φ (o.elim 0 MvPowerSeries.X)) = 0 := by
      funext o
      cases o with
      | none => exact map_zero φ
      | some i =>
        exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨i,rfl⟩)
    rw [hz,MvPolynomial.aeval_zero,hF,map_zero]
  have hu : IsUnit ((liftZ F).derivative.eval 0) := by
    rw [derivative_liftZ,eval_liftZ,MvPowerSeries.isUnit_iff_constantCoeff,
      zeroCoeff_aeval,isUnit_iff_ne_zero]
    exact hD
  let : IsAdicComplete I (MvPowerSeries σ K) :=
    inferInstanceAs (IsAdicComplete (Ideal.span (Set.range MvPowerSeries.X))
      (MvPowerSeries σ K))
  obtain ⟨h,hr,hh⟩ := hensel_nonmonic I (liftZ F) 0 hmem (hu.map (Ideal.Quotient.mk I))
  refine ⟨h,?_,?_⟩
  · have hi : I ≤ RingHom.ker (MvPowerSeries.constantCoeff (σ := σ) (R := K)) := by
      apply Ideal.span_le.mpr
      rintro _ ⟨i,rfl⟩
      simp
    apply hi
    simpa using hh
  · simpa [Polynomial.IsRoot,eval_liftZ] using hr

end SharpLogRamsey.ImplicitBranch

open Finset Finsupp
namespace SharpLogRamsey.FlatnessCore
variable {σ K : Type*} [Fintype σ] [DecidableEq σ] [Field K]
variable {p : ℕ} [CharP K p]

lemma cast_ne_zero_of_lt {n : ℕ} (hn : 0 < n) (hp : n < p) : (n : K) ≠ 0 := by
  rw [ne_eq, CharP.cast_eq_zero_iff K p]
  exact fun h => (Nat.le_of_dvd hn h).not_gt hp
omit [Fintype σ] in

lemma coeff_deriv_predecessor (f : MvPowerSeries σ K) (d : σ →₀ ℕ) (i : σ)
    (hi : 0 < d i) :
    MvPowerSeries.coeff (d-single i 1) (MvPowerSeries.pderiv _ i f) =
      MvPowerSeries.coeff d f * (d i : K) := by
  have h : single i 1 ≤ d := by
    intro j
    by_cases he : i = j
    · subst j; simpa using (Nat.succ_le_iff.mpr hi)
    · simp [single_eq_of_ne (Ne.symm he)]
  rw [MvPowerSeries.coeff_pderiv,tsub_add_cancel_of_le h,
    coe_tsub,Pi.sub_apply,single_eq_same,Nat.cast_sub (by omega),Nat.cast_one,sub_add_cancel]
omit [DecidableEq σ] in

lemma degree_pos_coordinate {d : σ →₀ ℕ} (hd : 0 < degree d) :
    ∃ i, 0 < d i := by
  by_contra! h
  have hz : d = 0 := by ext i; exact Nat.eq_zero_of_le_zero (h i)
  simp [hz] at hd
omit [Fintype σ] in

lemma coordinate_le_degree (d : σ →₀ ℕ) (i : σ) : d i ≤ degree d := by
  classical
  rw [degree_apply]
  by_cases hi : i ∈ d.support
  · exact single_le_sum (fun _ _ => Nat.zero_le _) hi
  · simp at hi
    simp [hi]

theorem coeff_zero_of_hessian_zero (h : MvPowerSeries σ K)
    (hh : ∀ i j, MvPowerSeries.pderiv _ i (MvPowerSeries.pderiv _ j h) = 0)
    (d : σ →₀ ℕ) (hd : 2 ≤ degree d) (hdp : degree d < p) :
    MvPowerSeries.coeff d h = 0 := by
  obtain ⟨i,hi⟩ := degree_pos_coordinate (d := d) (by omega)
  have hs : single i 1 ≤ d := by
    intro j
    by_cases he : i = j
    · subst j; simpa using (Nat.succ_le_iff.mpr hi)
    · simp [single_eq_of_ne (Ne.symm he)]
  let e := d-single i 1
  have hed : e + single i 1 = d := tsub_add_cancel_of_le hs
  have hedeg : degree e + 1 = degree d := by
    have := congrArg degree hed
    simpa using this
  obtain ⟨j,hj⟩ := degree_pos_coordinate (d := e) (by omega)
  have hc := coeff_deriv_predecessor (MvPowerSeries.pderiv _ i h) e j hj
  rw [hh j i,MvPowerSeries.coeff_zero] at hc
  have hej : (e j : K) ≠ 0 := cast_ne_zero_of_lt (p := p) hj
    (lt_of_le_of_lt (coordinate_le_degree e j) (by omega))
  have he0 : MvPowerSeries.coeff e (MvPowerSeries.pderiv _ i h) = 0 :=
    (mul_eq_zero.mp hc.symm).resolve_right hej
  have hc' := coeff_deriv_predecessor h d i hi
  change MvPowerSeries.coeff e (MvPowerSeries.pderiv _ i h) = _ at hc'
  rw [he0] at hc'
  exact (mul_eq_zero.mp hc'.symm).resolve_right
    (cast_ne_zero_of_lt (p := p) hi (lt_of_le_of_lt (coordinate_le_degree d i) hdp))

omit [Fintype σ] [DecidableEq σ] in

lemma mem_jetIdeal_iff (n : ℕ) (f : MvPowerSeries σ K) :
    f ∈ jetIdeal n ↔ ∀ d, degree d < n → MvPowerSeries.coeff d f = 0 := by
  constructor
  · intro h d hd
    exact MvPowerSeries.coeff_of_lt_order
      ((show ((degree d : ℕ) : ℕ∞) < n by exact_mod_cast hd).trans_le h)
  · exact MvPowerSeries.nat_le_order

theorem hessian_zero_affine_jet (h : MvPowerSeries σ K)
    (hh : ∀ i j, MvPowerSeries.pderiv _ i (MvPowerSeries.pderiv _ j h) = 0) :
    h - (MvPowerSeries.truncTotal 2 h : MvPolynomial σ K).toMvPowerSeries ∈ jetIdeal p := by
  rw [mem_jetIdeal_iff]
  intro d hdp
  rw [map_sub,MvPolynomial.coeff_coe]
  by_cases hd : degree d < 2
  · rw [MvPowerSeries.coeff_truncTotal _ hd,sub_self]
  · rw [MvPowerSeries.coeff_truncTotal_eq_zero _ (by omega),sub_zero]
    exact coeff_zero_of_hessian_zero h hh d (by omega) hdp

variable {τ R : Type*} [CommRing R] [Algebra K R]

lemma aeval_sub_mem (I : Ideal R) (x y : τ → R)
    (hxy : ∀ i, x i-y i ∈ I) (F : MvPolynomial τ K) :
    MvPolynomial.aeval x F-MvPolynomial.aeval y F ∈ I := by
  induction F using MvPolynomial.induction_on with
  | C c => simp
  | add f g hf hg => simpa only [map_add,add_sub_add_comm] using I.add_mem hf hg
  | mul_X f i hf =>
    simpa only [map_mul,MvPolynomial.aeval_X,
      show MvPolynomial.aeval x f*x i-MvPolynomial.aeval y f*y i =
        x i*(MvPolynomial.aeval x f-MvPolynomial.aeval y f)+
          MvPolynomial.aeval y f*(x i-y i) from by ring] using
      I.add_mem (I.mul_mem_left (x i) hf) (I.mul_mem_left _ (hxy i))

variable [Fintype τ] [DecidableEq τ]

omit [Fintype σ] [DecidableEq σ] [Fintype τ] [DecidableEq τ] in

lemma totalDegree_aeval_linear (x : τ → MvPolynomial σ K)
    (hx : ∀ i, (x i).totalDegree ≤ 1) (F : MvPolynomial τ K) :
    (MvPolynomial.aeval x F).totalDegree ≤ F.totalDegree := by
  classical
  conv_lhs => rw [F.as_sum]
  rw [map_sum]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro d hd
  rw [MvPolynomial.aeval_monomial]
  apply le_trans (MvPolynomial.totalDegree_mul _ _)
  simp only [MvPolynomial.algebraMap_eq, MvPolynomial.totalDegree_C,zero_add]
  calc
    _ ≤ ∑ i ∈ d.support, (x i ^ d i).totalDegree := MvPolynomial.totalDegree_finsetProd _ _
    _ ≤ ∑ i ∈ d.support, d i := by
      apply Finset.sum_le_sum
      intro i hi
      apply (MvPolynomial.totalDegree_pow _ _).trans
      simpa [Nat.mul_comm] using Nat.mul_le_mul_right (d i) (hx i)
    _ ≤ F.totalDegree := MvPolynomial.le_totalDegree hd
omit [Fintype σ] [DecidableEq σ] [Fintype τ] [DecidableEq τ] in

lemma toSeries_aeval (x : τ → MvPolynomial σ K) (F : MvPolynomial τ K) :
    (MvPolynomial.aeval x F).toMvPowerSeries =
      MvPolynomial.aeval (fun i => (x i).toMvPowerSeries) F := by
  induction F using MvPolynomial.induction_on with
  | C c => simp [← MvPowerSeries.c_eq_algebraMap]
  | add f g hf hg => simp only [map_add,MvPolynomial.coe_add,hf,hg]
  | mul_X f i hf => simp only [map_mul,MvPolynomial.coe_mul,MvPolynomial.aeval_X,hf]

omit [Fintype σ] in

lemma polynomial_eq_zero_of_jet {F : MvPolynomial σ K} {n : ℕ}
    (hF : F.totalDegree < n) (h : F.toMvPowerSeries ∈ jetIdeal n) : F = 0 := by
  ext d
  rw [MvPolynomial.coeff_zero]
  by_cases hd : d ∈ F.support
  · have hle := MvPolynomial.le_totalDegree hd
    have hc := (mem_jetIdeal_iff n F.toMvPowerSeries).mp h d (lt_of_le_of_lt hle hF)
    simpa using hc
  · exact MvPolynomial.notMem_support_iff.mp hd

theorem flat_branch_zero_plane (F : MvPolynomial (Option σ) K)
    (hF : F.totalDegree < p) (h : MvPowerSeries σ K)
    (hroot : MvPolynomial.aeval (fun o => o.elim h MvPowerSeries.X) F = 0)
    (hh : ∀ i j, MvPowerSeries.pderiv _ i (MvPowerSeries.pderiv _ j h) = 0) :
    MvPolynomial.aeval (fun o => o.elim (MvPowerSeries.truncTotal 2 h) MvPolynomial.X) F = 0 := by
  let lin := MvPowerSeries.truncTotal 2 h
  let x : Option σ → MvPolynomial σ K := fun o => o.elim lin MvPolynomial.X
  have hx : ∀ i, (x i).totalDegree ≤ 1 := by
    intro i
    cases i with
    | none =>
      have H := MvPowerSeries.totalDegree_truncTotal_lt h (by norm_num : (2:ℕ) ≠ 0)
      change lin.totalDegree ≤ 1
      dsimp [lin]
      omega
    | some i => exact (MvPolynomial.totalDegree_X (R := K) i).le
  apply polynomial_eq_zero_of_jet (n := p)
  · exact (totalDegree_aeval_linear x hx F).trans_lt hF
  · have H := aeval_sub_mem (jetIdeal p)
      (fun o => o.elim h MvPowerSeries.X) (fun i => (x i).toMvPowerSeries) (fun i => ?_) F
    · rw [hroot,zero_sub] at H
      rw [toSeries_aeval]
      exact neg_mem_iff.mp H
    cases i with
    | none => exact hessian_zero_affine_jet h hh
    | some i => simp [x]

lemma deriv_aeval (D : Derivation K R R) (x : τ → R) (F : MvPolynomial τ K) :
    D (MvPolynomial.aeval x F) =
      ∑ i, MvPolynomial.aeval x (MvPolynomial.pderiv i F) * D (x i) := by
  induction F using MvPolynomial.induction_on with
  | C c => simp
  | add f g hf hg => simp [hf,hg,add_mul,Finset.sum_add_distrib]
  | mul_X f j hf =>
    simp only [map_mul,MvPolynomial.aeval_X,Derivation.leibniz,smul_eq_mul,
      map_add,MvPolynomial.pderiv_X]
    simp only [
      add_mul,Finset.sum_add_distrib]
    rw [hf,Finset.mul_sum]
    congr 1
    · simp [Pi.single_apply]
    · apply Finset.sum_congr rfl
      intro i hi
      ring

lemma deriv2_aeval (D E : Derivation K R R) (x : τ → R) (F : MvPolynomial τ K) :
    D (E (MvPolynomial.aeval x F)) =
      (∑ j, ∑ i, MvPolynomial.aeval x (MvPolynomial.pderiv i
        (MvPolynomial.pderiv j F)) * D (x i) * E (x j)) +
      ∑ j, MvPolynomial.aeval x (MvPolynomial.pderiv j F) * D (E (x j)) := by
  rw [deriv_aeval E,map_sum]
  simp only [Derivation.leibniz,smul_eq_mul,Finset.sum_add_distrib]
  rw [add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  rw [deriv_aeval D,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

lemma branch_second_sum (h : MvPowerSeries σ K) (g : Option σ → MvPowerSeries σ K)
    (a b : σ) :
    (∑ j, g j * MvPowerSeries.pderiv _ a
      (MvPowerSeries.pderiv _ b (branchPoint h j))) =
    g none * MvPowerSeries.pderiv _ a (MvPowerSeries.pderiv _ b h) := by
  rw [Fintype.sum_option]
  simp [branchPoint,MvPowerSeries.pderiv_X,Pi.single_apply,apply_ite]

end SharpLogRamsey.FlatnessCore
end
end
end

end OAI
end

section
-- module Solutions.OAIQ060_R5.SharpRamsey_Geometry_HessianTangent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Incidence bounds for rich lines and finite point configurations. -/

section
section
section
open Finset Finsupp
namespace SharpLogRamsey.FlatnessCore
variable {σ K : Type*} [Fintype σ] [DecidableEq σ] [Field K]
variable {p : ℕ} [CharP K p]
variable {τ R : Type*} [CommRing R] [Algebra K R]
variable [Fintype τ] [DecidableEq τ]
lemma hessian_zero_of_tangent_zero (F : MvPolynomial (Option σ) K)
    (h : MvPowerSeries σ K) (hroot : MvPolynomial.aeval (branchPoint h) F = 0)
    (hu : IsUnit (MvPolynomial.aeval (branchPoint h) (MvPolynomial.pderiv none F)))
    (ht : ∀ a b, (∑ j, ∑ i, MvPolynomial.aeval (branchPoint h)
      (MvPolynomial.pderiv i (MvPolynomial.pderiv j F)) *
        branchTangent h a i * branchTangent h b j) = 0) :
    ∀ a b, MvPowerSeries.pderiv _ a (MvPowerSeries.pderiv _ b h) = 0 := by
  intro a b
  have H := deriv2_aeval (MvPowerSeries.pderiv _ a) (MvPowerSeries.pderiv _ b)
    (branchPoint h) F
  rw [hroot,map_zero,map_zero] at H
  change 0 = (∑ j, ∑ i, _ * branchTangent h a i * branchTangent h b j) + _ at H
  rw [ht a b,zero_add,branch_second_sum] at H
  exact (IsUnit.mul_right_eq_zero hu).mp H.symm

omit [Fintype σ] in

lemma aeval_scaledTangent (x : Option σ → R) (F : MvPolynomial (Option σ) K)
    (a : σ) (i : Option σ) :
    MvPolynomial.aeval x (scaledTangent (fun o => MvPolynomial.pderiv o F) a i) =
    scaledTangent (fun o => MvPolynomial.aeval x (MvPolynomial.pderiv o F)) a i := by
  cases i with
  | none => simp [scaledTangent]
  | some i => by_cases hi : i = a <;> simp [scaledTangent,hi]

lemma first_branch_derivative (F : MvPolynomial (Option σ) K)
    (h : MvPowerSeries σ K) (a : σ) :
    MvPowerSeries.pderiv _ a (MvPolynomial.aeval (branchPoint h) F) =
      MvPolynomial.aeval (branchPoint h) (MvPolynomial.pderiv none F) *
        MvPowerSeries.pderiv _ a h +
      MvPolynomial.aeval (branchPoint h) (MvPolynomial.pderiv (some a) F) := by
  rw [deriv_aeval,Fintype.sum_option]
  simp [branchPoint,MvPowerSeries.pderiv_X,Pi.single_apply]

lemma scaled_branch_tangent (F : MvPolynomial (Option σ) K)
    (h : MvPowerSeries σ K) (hroot : MvPolynomial.aeval (branchPoint h) F = 0)
    (a : σ) (i : Option σ) :
    MvPolynomial.aeval (branchPoint h) (MvPolynomial.pderiv none F) *
      branchTangent h a i =
      scaledTangent (fun o => MvPolynomial.aeval (branchPoint h)
        (MvPolynomial.pderiv o F)) a i := by
  cases i with
  | none =>
    have H := first_branch_derivative F h a
    rw [hroot,map_zero] at H
    change _ * MvPowerSeries.pderiv _ a h = -_
    exact eq_neg_of_add_eq_zero_left H.symm
  | some i => simp [branchTangent,branchPoint,scaledTangent,MvPowerSeries.pderiv_X,
      Pi.single_apply,mul_ite]

lemma flatness_root_implies_hessian_zero (F : MvPolynomial (Option σ) K)
    (h : MvPowerSeries σ K) (hroot : MvPolynomial.aeval (branchPoint h) F = 0)
    (hu : IsUnit (MvPolynomial.aeval (branchPoint h) (MvPolynomial.pderiv none F)))
    (hflat : ∀ a b, MvPolynomial.aeval (branchPoint h) (flatnessPolynomial F a b) = 0) :
    ∀ a b, MvPowerSeries.pderiv _ a (MvPowerSeries.pderiv _ b h) = 0 := by
  apply hessian_zero_of_tangent_zero F h hroot hu
  intro a b
  let z := MvPolynomial.aeval (branchPoint h) (MvPolynomial.pderiv none F)
  have H := hflat a b
  simp only [flatnessPolynomial,map_sum,map_mul,aeval_scaledTangent] at H
  have he : MvPolynomial.aeval (branchPoint h) (flatnessPolynomial F a b) =
      z*z*(∑ j, ∑ i, MvPolynomial.aeval (branchPoint h)
        (MvPolynomial.pderiv i (MvPolynomial.pderiv j F)) *
          branchTangent h a i * branchTangent h b j) := by
    simp only [flatnessPolynomial,map_sum,map_mul,aeval_scaledTangent,
      ← scaled_branch_tangent F h hroot,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    apply Finset.sum_congr rfl
    intro i hi
    dsimp [z]
    ring
  rw [hflat a b] at he
  exact (IsUnit.mul_right_eq_zero (hu.mul hu)).mp he.symm

end SharpLogRamsey.FlatnessCore

namespace SharpLogRamsey.LocalFlatness
open SharpLogRamsey.FlatnessCore
variable {σ K : Type*} [Fintype σ] [DecidableEq σ] [Field K]
omit [Fintype σ] [DecidableEq σ] in

lemma branch_constantCoeff (h : MvPowerSeries σ K)
    (hh : MvPowerSeries.constantCoeff h = 0) (F : MvPolynomial (Option σ) K) :
    MvPowerSeries.constantCoeff (MvPolynomial.aeval (branchPoint h) F) =
      MvPolynomial.constantCoeff F := by
  induction F using MvPolynomial.induction_on with
  | C c => simp [← MvPowerSeries.c_eq_algebraMap]
  | add f g hf hg => simp [hf,hg]
  | mul_X f i hf => cases i <;> simp [branchPoint,hh]
omit [Fintype σ] [DecidableEq σ] in

lemma rename_aeval (lin : MvPolynomial σ K) (G : MvPolynomial (Option σ) K) :
    MvPolynomial.rename Option.some (MvPolynomial.aeval
      (fun o => o.elim lin MvPolynomial.X) G) =
    MvPolynomial.aeval (fun o => o.elim (MvPolynomial.rename Option.some lin)
      (fun i => MvPolynomial.X (some i))) G := by
  induction G using MvPolynomial.induction_on with
  | C c => simp
  | add f g hf hg => simp only [map_add,hf,hg]
  | mul_X f i hf => cases i <;> simp only [map_mul,MvPolynomial.aeval_X,hf,
      Option.elim_none,Option.elim_some,MvPolynomial.rename_X]

omit [Fintype σ] [DecidableEq σ] in

lemma plane_factor_of_zero (lin : MvPolynomial σ K) (G : MvPolynomial (Option σ) K)
    (hz : MvPolynomial.aeval (fun o => o.elim lin MvPolynomial.X) G = 0) :
    MvPolynomial.X none - MvPolynomial.rename Option.some lin ∣ G := by
  let L : MvPolynomial (Option σ) K := MvPolynomial.X none-MvPolynomial.rename Option.some lin
  let I := Ideal.span ({L} : Set (MvPolynomial (Option σ) K))
  have he : MvPolynomial.aeval (fun o => o.elim (MvPolynomial.rename Option.some lin)
      (fun i => MvPolynomial.X (some i))) G = 0 := by
    rw [← rename_aeval,hz,map_zero]
  have H := aeval_sub_mem I (fun o => MvPolynomial.X o)
    (fun o => o.elim (MvPolynomial.rename Option.some lin) (fun i => MvPolynomial.X (some i)))
    (fun o => by cases o; exact Ideal.subset_span (Set.mem_singleton L); simp) G
  rw [he,sub_zero,MvPolynomial.aeval_X_left_apply] at H
  exact Ideal.mem_span_singleton.mp H

theorem exists_plane_factor_of_flatness {p : ℕ} [CharP K p]
    (G F : MvPolynomial (Option σ) K) (hdeg : G.totalDegree < p)
    (hdiv : F ∣ G) (hF : MvPolynomial.constantCoeff F = 0)
    (hDz : MvPolynomial.constantCoeff (MvPolynomial.pderiv none G) ≠ 0)
    (hflat : ∀ a b, F ∣ flatnessPolynomial G a b) :
    ∃ lin : MvPolynomial σ K, lin.totalDegree ≤ 1 ∧
      MvPolynomial.constantCoeff lin = 0 ∧
      MvPolynomial.X none-MvPolynomial.rename Option.some lin ∣ G := by
  obtain ⟨J,hJ⟩ := hdiv
  have hG : MvPolynomial.constantCoeff G = 0 := by simp [hJ,hF]
  have hJ0 : MvPolynomial.constantCoeff J ≠ 0 := by
    intro hz
    apply hDz
    simp [hJ,Derivation.leibniz,smul_eq_mul,hF,hz]
  obtain ⟨h,hh,hr⟩ := ImplicitBranch.exists_formal_branch G hG hDz
  change MvPolynomial.aeval (branchPoint h) G = 0 at hr
  have hJu : IsUnit (MvPolynomial.aeval (branchPoint h) J) := by
    rw [MvPowerSeries.isUnit_iff_constantCoeff,branch_constantCoeff h hh,isUnit_iff_ne_zero]
    exact hJ0
  have hFr : MvPolynomial.aeval (branchPoint h) F = 0 := by
    rw [hJ,map_mul] at hr
    exact (IsUnit.mul_left_eq_zero hJu).mp hr
  have hu : IsUnit (MvPolynomial.aeval (branchPoint h) (MvPolynomial.pderiv none G)) := by
    rw [MvPowerSeries.isUnit_iff_constantCoeff,branch_constantCoeff h hh,isUnit_iff_ne_zero]
    exact hDz
  have hf : ∀ a b, MvPolynomial.aeval (branchPoint h) (flatnessPolynomial G a b) = 0 := by
    intro a b
    obtain ⟨V,hV⟩ := hflat a b
    simp [hV,hFr]
  have hess := flatness_root_implies_hessian_zero G h hr hu hf
  have hz := flat_branch_zero_plane G hdeg h hr hess
  refine ⟨MvPowerSeries.truncTotal 2 h,?_,?_,plane_factor_of_zero _ G hz⟩
  · have H := MvPowerSeries.totalDegree_truncTotal_lt h (by norm_num : (2:ℕ) ≠ 0)
    omega
  · simpa [MvPowerSeries.constantCoeff_truncTotal_eq_ite] using hh

end SharpLogRamsey.LocalFlatness

open scoped BigOperators
open MvPolynomial Finsupp
namespace SharpLogRamsey.PolynomialGeometry
variable {σ K : Type*} [Field K]

lemma totalDegree_pderiv_lt (F : MvPolynomial σ K) (i : σ)
    (hi : pderiv i F ≠ 0) : (pderiv i F).totalDegree < F.totalDegree := by
  classical
  obtain ⟨d,hd,he⟩ := Finset.exists_mem_eq_sup _ (MvPolynomial.support_nonempty.mpr hi)
    (fun d : σ →₀ ℕ => d.sum fun _ e => e)
  have hc : F.coeff (d+Finsupp.single i 1) ≠ 0 := by
    have H := MvPolynomial.mem_support_iff.mp hd
    rw [MvPolynomial.coeff_pderiv] at H
    exact (mul_ne_zero_iff.mp H).1
  have H := MvPolynomial.le_totalDegree (MvPolynomial.mem_support_iff.mpr hc)
  change Finsupp.degree (d+Finsupp.single i 1) ≤ F.totalDegree at H
  have H' : d.degree+1 ≤ F.totalDegree := by
    simpa only [map_add, Finsupp.degree_single] using H
  change (pderiv i F).support.sup (fun d : σ →₀ ℕ => d.sum fun _ e => e) < F.totalDegree
  rw [he]
  exact H'

lemma not_dvd_pderiv (F : MvPolynomial σ K) (i : σ) (hi : pderiv i F ≠ 0) :
    ¬F ∣ pderiv i F := by
  intro h
  exact (totalDegree_pderiv_lt F i hi).not_ge
    (MvPolynomial.totalDegree_le_of_dvd_of_isDomain h hi)

lemma not_dvd_squarefree_derivative (G F : MvPolynomial σ K)
    (hs : Squarefree G) (hF : Irreducible F) (hd : F ∣ G) (i : σ)
    (hi : pderiv i F ≠ 0) : ¬ F ∣ pderiv i G := by
  obtain ⟨J,rfl⟩ := hd
  intro h
  have hp : Prime F := irreducible_iff_prime.mp hF
  have hn : ¬F ∣ J := by
    intro hj
    exact hF.not_isUnit (hs F (mul_dvd_mul dvd_rfl hj))
  have he : pderiv i (F*J) = pderiv i F*J+F*pderiv i J := by
    rw [MvPolynomial.pderiv_mul]
  rw [he,dvd_add_left (dvd_mul_right F _)] at h
  rcases hp.dvd_mul.mp h with h|h
  · exact not_dvd_pderiv F i hi h
  · exact hn h

lemma totalDegree_pos_of_irreducible (F : MvPolynomial σ K) (hF : Irreducible F) :
    0 < F.totalDegree := by
  by_contra! h
  have he : F = C (F.coeff 0) := totalDegree_eq_zero_iff_eq_C.mp (Nat.eq_zero_of_le_zero h)
  have hc : F.coeff 0 ≠ 0 := by intro hc; apply hF.ne_zero; rw [he,hc,map_zero]
  exact hF.not_isUnit (isUnit_iff_totalDegree_of_isReduced.mpr
    ⟨isUnit_iff_ne_zero.mpr hc,Nat.eq_zero_of_le_zero h⟩)

lemma exists_nonzero_pderiv {p : ℕ} [CharP K p]
    (F : MvPolynomial σ K) (hpos : 0 < F.totalDegree) (hdeg : F.totalDegree < p) :
    ∃ i, pderiv i F ≠ 0 := by
  classical
  have hF : F ≠ 0 := by intro he; simp [he] at hpos
  obtain ⟨d,hd,he⟩ := Finset.exists_mem_eq_sup F.support (support_nonempty.mpr hF)
    (fun d : σ →₀ ℕ => d.sum fun _ e => e)
  change F.totalDegree = d.degree at he
  have hdz : d ≠ 0 := by intro hd0; simp [hd0] at he; omega
  obtain ⟨i,hi⟩ := Finsupp.ne_iff.mp hdz
  have hi0 : 0 < d i := Nat.pos_of_ne_zero hi
  have hdi : d i ≤ d.degree := by
    rw [Finsupp.degree_apply]
    exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finsupp.mem_support_iff.mpr hi)
  have hcast : (d i : K) ≠ 0 := by
    rw [ne_eq,CharP.cast_eq_zero_iff K p]
    intro H
    have := Nat.le_of_dvd hi0 H
    omega
  have hs : Finsupp.single i 1 ≤ d := by
    intro j
    by_cases hij : i = j
    · subst j; simpa using (Nat.succ_le_iff.mpr hi0)
    · simp [Finsupp.single_eq_of_ne (Ne.symm hij)]
  refine ⟨i,fun hz => ?_⟩
  have hc := congrArg (fun poly : MvPolynomial σ K => poly.coeff (d-Finsupp.single i 1)) hz
  rw [coeff_pderiv,tsub_add_cancel_of_le hs,MvPolynomial.coeff_zero] at hc
  have hc' : F.coeff d * (d i : K) = 0 := by
    simpa [Finsupp.coe_tsub,Pi.sub_apply,Finsupp.single_eq_same,
      Nat.cast_sub (show 1 ≤ d i by omega)] using hc
  exact (mul_ne_zero (MvPolynomial.mem_support_iff.mp hd) hcast) hc'

variable [Finite σ] [IsAlgClosed K]

lemma exists_zero_not_zero (F D : MvPolynomial σ K)
    (hF : Irreducible F) (hD : ¬F ∣ D) :
    ∃ x : σ → K, aeval x F = 0 ∧ aeval x D ≠ 0 := by
  classical
  let I : Ideal (MvPolynomial σ K) := Ideal.span {F}
  let : I.IsPrime := (Ideal.span_singleton_prime hF.ne_zero).mpr
    (irreducible_iff_prime.mp hF)
  by_contra! H
  have hv : D ∈ MvPolynomial.vanishingIdeal K (MvPolynomial.zeroLocus K I) := by
    intro x hx
    apply H x
    exact hx F (Ideal.subset_span (Set.mem_singleton F))
  rw [MvPolynomial.IsPrime.vanishingIdeal_zeroLocus] at hv
  exact hD (Ideal.mem_span_singleton.mp hv)

lemma exists_nonsingular_factor_zero (G F : MvPolynomial σ K)
    (hs : Squarefree G) (hF : Irreducible F) (hd : F ∣ G) (i : σ)
    (hi : pderiv i F ≠ 0) :
    ∃ x : σ → K, aeval x F = 0 ∧ aeval x (pderiv i G) ≠ 0 :=
  exists_zero_not_zero F _ hF (not_dvd_squarefree_derivative G F hs hF hd i hi)

end SharpLogRamsey.PolynomialGeometry

open scoped BigOperators
open MvPolynomial
namespace SharpLogRamsey.Translation
variable {σ K : Type*} [Field K]

lemma pderiv_translate (x : σ → K) (i : σ) (F : MvPolynomial σ K) :
    pderiv i (translate x F) = translate x (pderiv i F) := by
  classical
  induction F using MvPolynomial.induction_on with
  | C c => simp
  | add f g hf hg => simp only [map_add,hf,hg]
  | mul_X f j hf =>
    simp only [map_mul,translate_X,MvPolynomial.pderiv_mul,map_add,hf,
      MvPolynomial.pderiv_X,MvPolynomial.pderiv_C,add_zero]
    simp only [Pi.single_apply]
    split_ifs <;> simp

lemma constantCoeff_translate (x : σ → K) (F : MvPolynomial σ K) :
    constantCoeff (translate x F) = aeval x F := by
  induction F using MvPolynomial.induction_on with
  | C c => simp
  | add f g hf hg => simp only [map_add,hf,hg]
  | mul_X f i hf => simp [hf]

lemma translate_nonunit (x : σ → K) {F : MvPolynomial σ K} (h : ¬IsUnit F) :
    ¬IsUnit (translate x F) := by
  intro hu
  apply h
  simpa using hu.map (translate (-x))
end SharpLogRamsey.Translation

namespace SharpLogRamsey.GlobalFlatness
open MvPolynomial SharpLogRamsey.FlatnessCore SharpLogRamsey.Translation
variable {σ K : Type*} [Fintype σ] [DecidableEq σ] [Field K]

lemma totalDegree_translate_le {τ : Type*} [Fintype τ] (x : τ → K) (F : MvPolynomial τ K) :
    (Translation.translate x F).totalDegree ≤ F.totalDegree := by
  classical
  apply totalDegree_aeval_linear
  intro i
  apply (totalDegree_add _ _).trans
  simp

lemma translate_flatness (x : Option σ → K) (G : MvPolynomial (Option σ) K) (a b : σ) :
    Translation.translate x (flatnessPolynomial G a b) = flatnessPolynomial (Translation.translate x G) a b := by
  simp only [flatnessPolynomial,map_sum,map_mul]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro i hi
  have ht : ∀ c k, Translation.translate x (scaledTangent (fun o => pderiv o G) c k) =
      scaledTangent (fun o => pderiv o (Translation.translate x G)) c k := by
    intro c k
    cases k with
    | none => simp [scaledTangent,pderiv_translate]
    | some k => by_cases h : k = c <;> simp [scaledTangent,h,pderiv_translate]
  rw [ht,ht,← pderiv_translate,← pderiv_translate]

theorem plane_factor_of_flatness {p : ℕ} [CharP K p] [IsAlgClosed K]
    (G F : MvPolynomial (Option σ) K) (hdeg : G.totalDegree < p)
    (hs : Squarefree G) (hF : Irreducible F) (hdiv : F ∣ G)
    (hDzF : pderiv none F ≠ 0) (hflat : ∀ a b, F ∣ flatnessPolynomial G a b) :
    ∃ L : MvPolynomial (Option σ) K, ¬IsUnit L ∧ L.totalDegree ≤ 1 ∧ L ∣ G := by
  obtain ⟨x,hx,hDx⟩ := PolynomialGeometry.exists_nonsingular_factor_zero
    G F hs hF hdiv none hDzF
  have hpl := LocalFlatness.exists_plane_factor_of_flatness
    (Translation.translate x G) (Translation.translate x F)
    ((totalDegree_translate_le x G).trans_lt hdeg) (map_dvd (Translation.translate x) hdiv)
    (by rwa [constantCoeff_translate])
    (by rwa [pderiv_translate,constantCoeff_translate])
    (fun a b => by rw [← translate_flatness]; exact map_dvd (Translation.translate x) (hflat a b))
  obtain ⟨lin,hlin,hlin0,hlind⟩ := hpl
  let L : MvPolynomial (Option σ) K := X none-rename Option.some lin
  have hL0 : constantCoeff L = 0 := by simp [L,hlin0]
  have hLu : ¬IsUnit L := by
    intro hu
    have H := hu.map (constantCoeff : MvPolynomial (Option σ) K →+* K)
    rw [hL0] at H
    exact not_isUnit_zero H
  have hLd : L.totalDegree ≤ 1 := by
    apply (totalDegree_sub _ _).trans
    apply max_le
    · exact (totalDegree_X none).le
    · exact (totalDegree_rename_le _ _).trans hlin
  refine ⟨Translation.translate (-x) L,translate_nonunit _ hLu,
    (totalDegree_translate_le _ _).trans hLd,?_⟩
  simpa only [translate_neg_translate] using map_dvd (Translation.translate (-x)) hlind

lemma nonplane_factor_not_flat {p : ℕ} [CharP K p] [IsAlgClosed K]
    (G F : MvPolynomial (Option σ) K) (hdeg : G.totalDegree < p)
    (hs : Squarefree G) (hF : Irreducible F) (hdiv : F ∣ G)
    (hDzF : pderiv none F ≠ 0)
    (hn : ∀ L : MvPolynomial (Option σ) K, L ∣ G → L.totalDegree ≤ 1 → IsUnit L) :
    ∃ a b, ¬ F ∣ flatnessPolynomial G a b := by
  by_contra! h
  obtain ⟨L,hu,hd,hdv⟩ := plane_factor_of_flatness G F hdeg hs hF hdiv hDzF h
  exact hu (hn L hdv hd)
end SharpLogRamsey.GlobalFlatness

open scoped BigOperators
open Finset MvPolynomial UniqueFactorizationMonoid
namespace SharpLogRamsey.CoprimeCombination
variable {σ ι K : Type*} [Fintype ι] [Field K] [Infinite K]

theorem exists_coprime_combination (G : MvPolynomial σ K) (hG : G ≠ 0)
    (Q : ι → MvPolynomial σ K)
    (h : ∀ F : MvPolynomial σ K, Irreducible F → F ∣ G → ∃ i, ¬F ∣ Q i) :
    ∃ c : ι → K, IsRelPrime G (∑ i, c i • Q i) := by
  classical
  let : NormalizationMonoid (MvPolynomial σ K) := UniqueFactorizationMonoid.strongNormalizationMonoid.toNormalizationMonoid
  let S := (normalizedFactors G).toFinset
  let P (F : S) : Submodule K (ι → K) :=
    ((Ideal.span ({F.val} : Set (MvPolynomial σ K))).restrictScalars K).comap (combinationMap Q)
  have hp : ∀ F, P F ≠ ⊤ := by
    intro F ht
    have hfm : F.val ∈ normalizedFactors G := Multiset.mem_toFinset.mp F.property
    obtain ⟨i,hi⟩ := h F.val (prime_of_normalized_factor _ hfm).irreducible
      (dvd_of_mem_normalizedFactors hfm)
    have H : Pi.single i 1 ∈ P F := ht ▸ Submodule.mem_top
    change combinationMap Q (Pi.single i 1) ∈ Ideal.span ({F.val} : Set (MvPolynomial σ K)) at H
    simp [Pi.single_apply] at H
    exact hi (Ideal.mem_span_singleton.mp H)
  obtain ⟨c,hc⟩ := Submodule.exists_forall_notMem_of_forall_ne_top P hp
  refine ⟨c,(isRelPrime_iff_no_prime_factors hG).mpr ?_⟩
  intro F hFG hFQ hFp
  obtain ⟨J,hJ,hassoc⟩ := exists_mem_normalizedFactors_of_dvd hG hFp.irreducible hFG
  apply hc ⟨J,Multiset.mem_toFinset.mpr hJ⟩
  change combinationMap Q c ∈ Ideal.span ({J} : Set (MvPolynomial σ K))
  rw [combinationMap_apply,Ideal.mem_span_singleton]
  exact hassoc.dvd_iff_dvd_left.mp hFQ
end SharpLogRamsey.CoprimeCombination
end
end
end

end OAI
end

section
-- module Solutions.OAIQ060_R5.SharpRamsey_Geometry_TotalDegreeCombination
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Incidence bounds for rich lines and finite point configurations. -/

section
section
section
open Finset Finsupp
open scoped BigOperators
open MvPolynomial Finsupp
open scoped BigOperators
open MvPolynomial
open scoped BigOperators
open Finset MvPolynomial UniqueFactorizationMonoid
namespace SharpLogRamsey.CoprimeCombination
variable {σ ι K : Type*} [Fintype ι] [Field K] [Infinite K]
omit [Infinite K] in
lemma totalDegree_combination_le (Q : ι → MvPolynomial σ K) (c : ι → K) (D : ℕ)
    (h : ∀ i, (Q i).totalDegree ≤ D) :
    (∑ i, c i • Q i).totalDegree ≤ D := by
  apply MvPolynomial.totalDegree_finsetSum_le
  intro i hi
  exact (MvPolynomial.totalDegree_smul_le _ _).trans (h i)
end SharpLogRamsey.CoprimeCombination

namespace SharpLogRamsey.NonplaneCertificate
open MvPolynomial FlatnessCore PolynomialGeometry
variable {K : Type*} [Field K]
noncomputable section

lemma squarefree_equiv {A B : Type*} [Monoid A] [Monoid B]
    (e : A ≃* B) {f : A} (h : Squarefree f) : Squarefree (e f) := by
  intro x hx
  have H : e.symm x*e.symm x ∣ f := by
    simpa only [map_mul,e.symm_apply_apply] using map_dvd e.symm hx
  have H' := (h _ H).map e
  simpa only [e.apply_symm_apply] using H'

lemma totalDegree_equiv_le {α β : Type*} (e : α ≃ β) (F : MvPolynomial α K) :
    (renameEquiv K e F).totalDegree ≤ F.totalDegree := totalDegree_rename_le _ _

lemma pderiv_equiv {α β : Type*} (e : α ≃ β) (F : MvPolynomial α K) (i : α) :
    pderiv (e i) (renameEquiv K e F) = renameEquiv K e (pderiv i F) :=
  pderiv_rename e.injective i F

lemma nonplane_witness {p : ℕ} [CharP K p] [IsAlgClosed K]
    (G F : MvPolynomial (Fin 3) K) (hG : G ≠ 0) (hdeg : G.totalDegree < p)
    (hs : Squarefree G) (hF : Irreducible F) (hdiv : F ∣ G)
    (hn : ∀ L : MvPolynomial (Fin 3) K, L ∣ G → L.totalDegree ≤ 1 → IsUnit L) :
    ∃ i : Index, ¬F ∣ flatFamily G i := by
  obtain ⟨i,hi⟩ := exists_nonzero_pderiv F
    (totalDegree_pos_of_irreducible F hF)
    ((totalDegree_le_of_dvd_of_isDomain hdiv hG).trans_lt hdeg)
  let e : Option (Fin 2) ≃ Fin 3 := (finSuccEquiv' i).symm
  let E := renameEquiv K e
  have hen : e none = i := finSuccEquiv'_symm_none i
  have hdn : pderiv none (E.symm F) ≠ 0 := by
    have he := pderiv_equiv e.symm F i
    have hnone : e.symm i = none := by rw [← hen]; simp
    rw [hnone] at he
    change pderiv none (E.symm F) = E.symm (pderiv i F) at he
    rw [he]
    exact fun h => hi (E.symm.injective (h.trans (map_zero E.symm).symm))
  obtain ⟨a,b,hab⟩ := GlobalFlatness.nonplane_factor_not_flat
    (E.symm G) (E.symm F)
    ((totalDegree_equiv_le e.symm G).trans_lt hdeg)
    (squarefree_equiv E.symm.toMulEquiv hs)
    ((MulEquiv.irreducible_iff E.symm).mpr hF) (map_dvd E.symm hdiv) hdn
    (fun L hd hdl => by
      have hL := hn (E L) (by simpa only [E.apply_symm_apply] using map_dvd E hd)
        ((totalDegree_equiv_le e L).trans hdl)
      exact (isUnit_map_iff E L).mp hL)
  refine ⟨⟨e,a,b⟩,fun hd => hab ?_⟩
  have H := map_dvd E.symm hd
  change E.symm F ∣ E.symm (E (flatnessPolynomial (E.symm G) a b)) at H
  simpa only [E.symm_apply_apply] using H

lemma totalDegree_partial_le {α : Type*} (F : MvPolynomial α K) (i : α) :
    (pderiv i F).totalDegree ≤ F.totalDegree := by
  by_cases h : pderiv i F = 0
  · simp [h]
  · exact (totalDegree_pderiv_lt F i h).le

lemma totalDegree_tangent_le (G : MvPolynomial (Option (Fin 2)) K) (a : Fin 2)
    (i : Option (Fin 2)) :
    (scaledTangent (fun i => pderiv i G) a i).totalDegree ≤ G.totalDegree := by
  cases i with
  | none => simpa [scaledTangent] using totalDegree_partial_le G (some a)
  | some i =>
    by_cases hi : i = a
    · simpa [scaledTangent,hi] using totalDegree_partial_le G none
    · simp [scaledTangent,hi]

lemma totalDegree_flatness_le (G : MvPolynomial (Option (Fin 2)) K) (a b : Fin 2) :
    (flatnessPolynomial G a b).totalDegree ≤ 3*G.totalDegree := by
  apply totalDegree_finsetSum_le
  intro j hj
  apply totalDegree_finsetSum_le
  intro i hi
  have H := totalDegree_mul (pderiv i (pderiv j G)*scaledTangent (fun i => pderiv i G) a i)
    (scaledTangent (fun i => pderiv i G) b j)
  have H' := totalDegree_mul (pderiv i (pderiv j G)) (scaledTangent (fun i => pderiv i G) a i)
  have H'' := (totalDegree_partial_le (pderiv j G) i).trans (totalDegree_partial_le G j)
  have H1 := totalDegree_tangent_le G a i
  have H2 := totalDegree_tangent_le G b j
  omega

lemma totalDegree_family_le (G : MvPolynomial (Fin 3) K) (i : Index) :
    (flatFamily G i).totalDegree ≤ 3*G.totalDegree := by
  exact (totalDegree_equiv_le _ _).trans ((totalDegree_flatness_le _ _ _).trans
    (Nat.mul_le_mul_left _ (totalDegree_equiv_le _ _)))

theorem exists_coprime_flat_combination {p : ℕ} [CharP K p] [IsAlgClosed K]
    (G : MvPolynomial (Fin 3) K) (hG : G ≠ 0) (hdeg : G.totalDegree < p)
    (hs : Squarefree G)
    (hn : ∀ L : MvPolynomial (Fin 3) K, L ∣ G → L.totalDegree ≤ 1 → IsUnit L) :
    ∃ c : Index → K, IsRelPrime G (∑ i, c i • flatFamily G i) ∧
      (∑ i, c i • flatFamily G i).totalDegree ≤ 3*G.totalDegree := by
  obtain ⟨c,hc⟩ := CoprimeCombination.exists_coprime_combination G hG (flatFamily G)
    (fun F hF hd => nonplane_witness G F hG hdeg hs hF hd hn)
  exact ⟨c,hc,CoprimeCombination.totalDegree_combination_le _ _ _ (totalDegree_family_le G)⟩
end
end SharpLogRamsey.NonplaneCertificate

open scoped BigOperators
open Finset MvPolynomial
namespace SharpLogRamsey.LineFlatness
variable {K σ R : Type*} [Field K] [Fintype σ] [DecidableEq σ]
  [CommRing R] [Algebra K R]

lemma deriv_aeval (D : Derivation K R R) (x : σ → R) (F : MvPolynomial σ K) :
    D (MvPolynomial.aeval x F) =
      ∑ i, MvPolynomial.aeval x (MvPolynomial.pderiv i F) * D (x i) := by
  induction F using MvPolynomial.induction_on with
  | C c => simp
  | add f g hf hg => simp [hf,hg,add_mul,Finset.sum_add_distrib]
  | mul_X f j hf =>
    simp only [map_mul,MvPolynomial.aeval_X,Derivation.leibniz,smul_eq_mul,
      map_add,MvPolynomial.pderiv_X]
    simp only [
      add_mul,Finset.sum_add_distrib]
    rw [hf,Finset.mul_sum]
    congr 1
    · simp [Pi.single_apply]
    · apply Finset.sum_congr rfl
      intro i hi
      ring

lemma deriv2_aeval (D E : Derivation K R R) (x : σ → R) (F : MvPolynomial σ K) :
    D (E (MvPolynomial.aeval x F)) =
      (∑ j, ∑ i, MvPolynomial.aeval x (MvPolynomial.pderiv i
        (MvPolynomial.pderiv j F)) * D (x i) * E (x j)) +
      ∑ j, MvPolynomial.aeval x (MvPolynomial.pderiv j F) * D (E (x j)) := by
  rw [deriv_aeval E,map_sum]
  simp only [Derivation.leibniz,smul_eq_mul,Finset.sum_add_distrib]
  rw [add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  rw [deriv_aeval D,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

omit [Fintype σ] [DecidableEq σ] in

lemma eval_restrictLine (x v : σ → K) (F : MvPolynomial σ K) (t : K) :
    (restrictLine x v F).eval t = eval (fun i => x i + v i*t) F := by
  induction F using MvPolynomial.induction_on with
  | C c => simp [restrictLine]
  | add f g hf hg => simp_all [restrictLine]
  | mul_X f i hf => simp_all [restrictLine]

lemma derivative_restrictLine (x v : σ → K) (F : MvPolynomial σ K) :
    Polynomial.derivative (restrictLine x v F) =
      ∑ i, restrictLine x v (pderiv i F) * Polynomial.C (v i) := by
  have H := deriv_aeval Polynomial.derivative'
    (fun i => Polynomial.C (x i) + Polynomial.C (v i) * Polynomial.X) F
  simpa [restrictLine] using H

lemma line_tangent (x v : σ → K) (F : MvPolynomial σ K)
    (h : restrictLine x v F = 0) :
    ∑ i, eval x (pderiv i F)*v i = 0 := by
  have H := congrArg (Polynomial.eval (0 : K)) (derivative_restrictLine x v F)
  simpa [h,Polynomial.eval_finsetSum,eval_restrictLine] using H.symm

lemma line_hessian (x v : σ → K) (F : MvPolynomial σ K)
    (h : restrictLine x v F = 0) :
    ∑ j, ∑ i, eval x (pderiv i (pderiv j F))*v i*v j = 0 := by
  have H := deriv2_aeval Polynomial.derivative' Polynomial.derivative'
    (fun i => Polynomial.C (x i) + Polynomial.C (v i) * Polynomial.X) F
  change Polynomial.derivative (Polynomial.derivative (restrictLine x v F)) = _ at H
  simp only [show ∀ i, Polynomial.derivative'
      (Polynomial.C (x i) + Polynomial.C (v i) * Polynomial.X) = Polynomial.C (v i)
      from fun i => by simp, show ∀ i, Polynomial.derivative' (Polynomial.C (v i)) = 0
      from fun i => by simp,mul_zero,sum_const_zero,add_zero] at H
  change Polynomial.derivative (Polynomial.derivative (restrictLine x v F)) =
    ∑ j, ∑ i, restrictLine x v (pderiv i (pderiv j F)) * Polynomial.C (v i) * Polynomial.C (v j) at H
  have E := congrArg (Polynomial.eval (0 : K)) H
  simpa [h,Polynomial.eval_finsetSum,eval_restrictLine] using E.symm
omit [Fintype σ] in

lemma pderiv_swap (F : MvPolynomial σ K) (i j : σ) :
    pderiv i (pderiv j F) = pderiv j (pderiv i F) := by
  induction F using MvPolynomial.induction_on with
  | C c => simp
  | add f g hf hg => simp [hf,hg]
  | mul_X f k hf =>
    by_cases hi : k = i <;> by_cases hj : k = j <;>
      simp [pderiv_X,Pi.single_apply,apply_ite,hi,hj,hf,add_comm,add_left_comm]
    all_goals split_ifs <;> simp_all

lemma quadratic_vandermonde (v : Fin 3 → Fin 2 → K) :
    (Matrix.of (fun (i j : Fin 3) => ![(v i 0)^2, v i 0*v i 1, (v i 1)^2] j)).det =
      (v 0 0*v 1 1-v 0 1*v 1 0) * (v 0 0*v 2 1-v 0 1*v 2 0) *
      (v 1 0*v 2 1-v 1 1*v 2 0) := by
  rw [Matrix.det_fin_three]
  simp only [Matrix.of_apply]
  dsimp
  ring

theorem binary_quadratic_three (v : Fin 3 → Fin 2 → K) (A B C : K)
    (h01 : v 0 0*v 1 1-v 0 1*v 1 0 ≠ 0)
    (h02 : v 0 0*v 2 1-v 0 1*v 2 0 ≠ 0)
    (h12 : v 1 0*v 2 1-v 1 1*v 2 0 ≠ 0)
    (hv : ∀ i, A*(v i 0)^2+B*(v i 0*v i 1)+C*(v i 1)^2 = 0) :
    A = 0 ∧ B = 0 ∧ C = 0 := by
  let M : Matrix (Fin 3) (Fin 3) K :=
    Matrix.of (fun i j => ![(v i 0)^2,v i 0*v i 1,(v i 1)^2] j)
  have hdet : IsUnit M.det := by
    rw [isUnit_iff_ne_zero,quadratic_vandermonde]
    exact mul_ne_zero (mul_ne_zero h01 h02) h12
  have hm : M.mulVec ![A,B,C] = 0 := by
    ext i
    simpa [M,Matrix.mulVec,dotProduct,Fin.sum_univ_succ,mul_comm,add_assoc] using hv i
  have E := congrArg (Matrix.mulVec M⁻¹) hm
  rw [Matrix.mulVec_mulVec,Matrix.nonsing_inv_mul M hdet,
    Matrix.one_mulVec,Matrix.mulVec_zero] at E
  exact ⟨congrFun E 0,congrFun E 1,congrFun E 2⟩

omit [DecidableEq σ] in

lemma hessian_smul_left (x : σ → K) (F : MvPolynomial σ K) (a : K) (u v : σ → K) :
    hessian x F (a • u) v = a*hessian x F u v := by
  simp only [hessian,Pi.smul_apply,smul_eq_mul,Finset.mul_sum]
  congr 1; ext j
  congr 1; ext i
  ring
omit [DecidableEq σ] in

lemma hessian_smul_right (x : σ → K) (F : MvPolynomial σ K) (a : K) (u v : σ → K) :
    hessian x F u (a • v) = a*hessian x F u v := by
  simp only [hessian,Pi.smul_apply,smul_eq_mul,Finset.mul_sum]
  congr 1; ext j
  congr 1; ext i
  ring
omit [DecidableEq σ] in

lemma hessian_add_left (x : σ → K) (F : MvPolynomial σ K) (u v w : σ → K) :
    hessian x F (u+v) w = hessian x F u w+hessian x F v w := by
  simp [hessian,mul_add,add_mul,sum_add_distrib]
omit [DecidableEq σ] in

lemma hessian_add_right (x : σ → K) (F : MvPolynomial σ K) (u v w : σ → K) :
    hessian x F u (v+w) = hessian x F u v+hessian x F u w := by
  simp [hessian,mul_add,sum_add_distrib]

lemma hessian_symm (x : σ → K) (F : MvPolynomial σ K) (u v : σ → K) :
    hessian x F u v = hessian x F v u := by
  unfold hessian
  rw [Finset.sum_comm]
  apply sum_congr rfl
  intro i hi
  apply sum_congr rfl
  intro j hj
  rw [pderiv_swap F i j]
  ring

lemma tangent_expansion (g v : Option (Fin 2) → K)
    (hv : ∑ i, g i*v i = 0) :
    g none • v = v (some 0) • scaledTangent g 0 + v (some 1) • scaledTangent g 1 := by
  ext i
  cases i with
  | none =>
    simp only [Fintype.sum_option,Fin.sum_univ_two] at hv
    simp only [Pi.smul_apply,Pi.add_apply,smul_eq_mul,scaledTangent,Option.elim_none]
    linear_combination hv
  | some i => fin_cases i <;> simp [scaledTangent,mul_comm]

lemma tangent_projection_independent (g : Option (Fin 2) → K) (hg : g none ≠ 0)
    (v : Fin 2 → Option (Fin 2) → K) (hv : ∀ a, ∑ i, g i*v a i = 0)
    (hli : LinearIndependent K v) :
    LinearIndependent K (fun a i => v a (some i)) := by
  rw [Fintype.linearIndependent_iff] at hli ⊢
  intro c hc
  apply hli c
  ext i
  have h0 := congrFun hc 0
  have h1 := congrFun hc 1
  simp only [Fin.sum_univ_two,Pi.add_apply,Pi.smul_apply,smul_eq_mul,Pi.zero_apply] at h0 h1 ⊢
  cases i with
  | some i => fin_cases i <;> assumption
  | none =>
    apply (mul_left_cancel₀ hg)
    rw [mul_zero]
    have h2 := hv 0
    have h3 := hv 1
    simp only [Fintype.sum_option,Fin.sum_univ_two] at h2 h3
    linear_combination c 0*h2+c 1*h3-g (some 0)*h0-g (some 1)*h1

lemma tangent_projection_det (g : Option (Fin 2) → K) (hg : g none ≠ 0)
    (u v : Option (Fin 2) → K) (hu : ∑ i, g i*u i = 0) (hv : ∑ i, g i*v i = 0)
    (hli : LinearIndependent K ![u,v]) :
    u (some 0)*v (some 1)-u (some 1)*v (some 0) ≠ 0 := by
  have hl := tangent_projection_independent g hg ![u,v]
    (fun i => by fin_cases i <;> assumption) hli
  let M : Matrix (Fin 2) (Fin 2) K := Matrix.of (fun i j => ![u,v] i (some j))
  have hM : IsUnit M := Matrix.linearIndependent_rows_iff_isUnit.mp hl
  have hD := (Matrix.isUnit_iff_isUnit_det M).mp hM
  simpa [M,Matrix.det_fin_two,isUnit_iff_ne_zero] using hD

theorem three_lines_flat (F : MvPolynomial (Option (Fin 2)) K)
    (x : Option (Fin 2) → K) (v : Fin 3 → Option (Fin 2) → K)
    (h2 : (2 : K) ≠ 0) (hz : eval x (pderiv none F) ≠ 0)
    (hlines : ∀ i, restrictLine x (v i) F = 0)
    (h01 : LinearIndependent K ![v 0,v 1])
    (h02 : LinearIndependent K ![v 0,v 2])
    (h12 : LinearIndependent K ![v 1,v 2]) :
    ∀ a b, hessian x F (scaledTangent (fun i => eval x (pderiv i F)) a)
      (scaledTangent (fun i => eval x (pderiv i F)) b) = 0 := by
  let g : Option (Fin 2) → K := fun i => eval x (pderiv i F)
  let t := scaledTangent g
  have ht (i : Fin 3) : ∑ a, g a*v i a = 0 := line_tangent x (v i) F (hlines i)
  have hH (i : Fin 3) : hessian x F (v i) (v i) = 0 := line_hessian x (v i) F (hlines i)
  have he (i : Fin 3) := tangent_expansion g (v i) (ht i)
  have hq (i : Fin 3) :
      hessian x F (t 0) (t 0)*(v i (some 0))^2 +
        (2*hessian x F (t 0) (t 1))*(v i (some 0)*v i (some 1)) +
      hessian x F (t 1) (t 1)*(v i (some 1))^2 = 0 := by
    have E : hessian x F (g none • v i) (g none • v i) = 0 := by
      rw [hessian_smul_left,hessian_smul_right,hH,mul_zero,mul_zero]
    rw [he,hessian_add_left,hessian_add_right,hessian_add_right] at E
    simp only [hessian_smul_left,hessian_smul_right] at E
    rw [hessian_symm x F (t 1) (t 0)] at E
    linear_combination E
  obtain ⟨h00,h01',h11⟩ := binary_quadratic_three
    (fun i a => v i (some a)) _ _ _
    (tangent_projection_det g hz _ _ (ht 0) (ht 1) h01)
    (tangent_projection_det g hz _ _ (ht 0) (ht 2) h02)
    (tangent_projection_det g hz _ _ (ht 1) (ht 2) h12) hq
  have h01z := (mul_eq_zero.mp h01').resolve_left h2
  intro a b
  fin_cases a <;> fin_cases b
  · exact h00
  · exact h01z
  · exact (hessian_symm x F (t 1) (t 0)).trans h01z
  · exact h11

lemma three_lines_all_tangents (F : MvPolynomial (Option (Fin 2)) K)
    (x : Option (Fin 2) → K) (v : Fin 3 → Option (Fin 2) → K)
    (h2 : (2 : K) ≠ 0) (hz : eval x (pderiv none F) ≠ 0)
    (hlines : ∀ i, restrictLine x (v i) F = 0)
    (h01 : LinearIndependent K ![v 0,v 1])
    (h02 : LinearIndependent K ![v 0,v 2])
    (h12 : LinearIndependent K ![v 1,v 2])
    (u w : Option (Fin 2) → K)
    (hu : ∑ i, eval x (pderiv i F)*u i = 0)
    (hw : ∑ i, eval x (pderiv i F)*w i = 0) : hessian x F u w = 0 := by
  let g := fun i => eval x (pderiv i F)
  have H := three_lines_flat F x v h2 hz hlines h01 h02 h12
  apply mul_left_cancel₀ (mul_ne_zero hz hz)
  rw [mul_zero]
  calc
    _ = hessian x F (g none • u) (g none • w) := by
      rw [hessian_smul_left,hessian_smul_right]; ring
    _ = 0 := by
      rw [tangent_expansion g u hu,tangent_expansion g w hw,
        hessian_add_left,hessian_add_right,hessian_add_right]
      simp only [hessian_smul_left,hessian_smul_right,g,H,mul_zero,add_zero]

variable {τ : Type*} [Fintype τ] [DecidableEq τ]
omit [DecidableEq σ] [DecidableEq τ] in
lemma hessian_rename (e : σ ≃ τ) (F : MvPolynomial σ K) (x u v : τ → K) :
    hessian x (renameEquiv K e F) u v = hessian (x ∘ e) F (u ∘ e) (v ∘ e) := by
  unfold hessian
  rw [← e.sum_comp]
  apply sum_congr rfl
  intro j hj
  rw [← e.sum_comp]
  apply sum_congr rfl
  intro i hi
  simp only [renameEquiv_apply,pderiv_rename e.injective,eval_rename,Function.comp_apply]
omit [Fintype σ] [DecidableEq σ] [Fintype τ] [DecidableEq τ] in

lemma restrictLine_rename (e : σ ≃ τ) (F : MvPolynomial σ K) (x v : τ → K) :
    restrictLine x v (renameEquiv K e F) = restrictLine (x ∘ e) (v ∘ e) F := by
  simp only [restrictLine,renameEquiv_apply,aeval_rename,Function.comp_def]
omit [DecidableEq σ] [DecidableEq τ] in

lemma tangent_rename (e : σ ≃ τ) (F : MvPolynomial σ K) (x v : τ → K) :
    (∑ i, eval x (pderiv i (renameEquiv K e F))*v i) =
      ∑ i, eval (x ∘ e) (pderiv i F)*(v ∘ e) i := by
  rw [← e.sum_comp]
  apply sum_congr rfl
  intro i hi
  simp only [renameEquiv_apply,pderiv_rename e.injective,eval_rename,Function.comp_apply]
omit [Fintype σ] [DecidableEq σ] [Fintype τ] [DecidableEq τ] in

lemma independent_rename (e : σ ≃ τ) (u v : τ → K)
    (h : LinearIndependent K ![u,v]) : LinearIndependent K ![u ∘ e,v ∘ e] := by
  let E := LinearEquiv.funCongrLeft K K e
  have H := h.map' E.toLinearMap E.ker
  change LinearIndependent K (fun i => ![u,v] i ∘ e) at H
  convert H using 1
  all_goals try with_reducible_and_instances rfl
  ext i j
  fin_cases i <;> rfl

theorem three_lines_tangent_zero (F : MvPolynomial (Fin 3) K)
    (x : Fin 3 → K) (v : Fin 3 → Fin 3 → K)
    (h2 : (2 : K) ≠ 0) (hn : ∃ i, eval x (pderiv i F) ≠ 0)
    (hlines : ∀ i, restrictLine x (v i) F = 0)
    (h01 : LinearIndependent K ![v 0,v 1])
    (h02 : LinearIndependent K ![v 0,v 2])
    (h12 : LinearIndependent K ![v 1,v 2])
    (u w : Fin 3 → K) (hu : ∑ i, eval x (pderiv i F)*u i = 0)
    (hw : ∑ i, eval x (pderiv i F)*w i = 0) : hessian x F u w = 0 := by
  obtain ⟨i,hi⟩ := hn
  let e : Option (Fin 2) ≃ Fin 3 := (finSuccEquiv' i).symm
  have hen : e none = i := finSuccEquiv'_symm_none i
  have hc (z : Fin 3 → K) : (z ∘ e) ∘ e.symm = z := by ext j; simp
  have hz : eval (x ∘ e) (pderiv none (renameEquiv K e.symm F)) ≠ 0 := by
    have he := pderiv_rename e.symm.injective i F
    have hnone : e.symm i = none := by rw [← hen]; simp
    rw [hnone] at he
    simpa only [renameEquiv_apply,he,eval_rename,hc] using hi
  have H := three_lines_all_tangents (renameEquiv K e.symm F) (x ∘ e)
    (fun j => v j ∘ e) h2 hz
    (fun j => by simpa only [restrictLine_rename,hc] using hlines j)
    (independent_rename e _ _ h01) (independent_rename e _ _ h02)
    (independent_rename e _ _ h12) (u ∘ e) (w ∘ e)
    (by simpa only [tangent_rename,hc] using hu)
    (by simpa only [tangent_rename,hc] using hw)
  simpa only [hessian_rename,hc] using H

end SharpLogRamsey.LineFlatness

end
end
end

end OAI
end

section
-- module Solutions.OAIQ060_R5.SharpRamsey_Geometry_ScaledTangentDot
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Incidence bounds for rich lines and finite point configurations. -/

section
section
section
open Finset Finsupp
open scoped BigOperators
open MvPolynomial Finsupp
open scoped BigOperators
open MvPolynomial
open scoped BigOperators
open Finset MvPolynomial UniqueFactorizationMonoid
open scoped BigOperators
open Finset MvPolynomial
namespace SharpLogRamsey.RichLinePolynomial
open MvPolynomial Finset
open FlatnessCore NonplaneCertificate
variable {K : Type*} [Field K]
lemma scaled_tangent_dot (g : Option (Fin 2) → K) (a : Fin 2) :
    ∑ i, g i*FlatnessCore.scaledTangent g a i = 0 := by
  simp [FlatnessCore.scaledTangent,Fintype.sum_option,mul_comm]

lemma eval_flatness (F : MvPolynomial (Option (Fin 2)) K) (x : Option (Fin 2) → K)
    (a b : Fin 2) : eval x (FlatnessCore.flatnessPolynomial F a b) =
    LineFlatness.hessian x F
      (FlatnessCore.scaledTangent (fun i => eval x (pderiv i F)) a)
      (FlatnessCore.scaledTangent (fun i => eval x (pderiv i F)) b) := by
  unfold FlatnessCore.flatnessPolynomial LineFlatness.hessian
  simp only [map_sum,map_mul]
  congr 1; ext j
  congr 1; ext i
  have he (a : Fin 2) (i : Option (Fin 2)) :
      eval x (FlatnessCore.scaledTangent (fun i => pderiv i F) a i) =
        FlatnessCore.scaledTangent (fun i => eval x (pderiv i F)) a i := by
    cases i with
    | none => simp [FlatnessCore.scaledTangent]
    | some i => by_cases hi : i = a <;> simp [FlatnessCore.scaledTangent,hi]
  rw [he,he]

theorem family_zero_at_three_lines (F : MvPolynomial (Fin 3) K)
    (x : Fin 3 → K) (v : Fin 3 → Fin 3 → K)
    (h2 : (2 : K) ≠ 0) (hl : ∀ i, LineFlatness.restrictLine x (v i) F = 0)
    (h01 : LinearIndependent K ![v 0,v 1])
    (h02 : LinearIndependent K ![v 0,v 2])
    (h12 : LinearIndependent K ![v 1,v 2]) (idx : Index) :
    eval x (flatFamily F idx) = 0 := by
  let e := idx.1
  let G := renameEquiv K e.symm F
  let y := x ∘ e
  let g := fun i => eval y (pderiv i G)
  have hc (z : Fin 3 → K) : (z ∘ e) ∘ e.symm = z := by ext i; simp
  have hge (i : Option (Fin 2)) : g i = eval x (pderiv (e i) F) := by
    have H := pderiv_rename e.symm.injective (e i) F
    simpa only [g,G,y,renameEquiv_apply,e.symm_apply_apply,eval_rename,hc] using congrArg (eval y) H
  change eval x (renameEquiv K e (flatnessPolynomial G idx.2.1 idx.2.2)) = 0
  rw [renameEquiv_apply,eval_rename,eval_flatness]
  change LineFlatness.hessian y G (FlatnessCore.scaledTangent g idx.2.1)
    (FlatnessCore.scaledTangent g idx.2.2) = 0
  by_cases hn : ∃ i, eval x (pderiv i F) ≠ 0
  · let u := FlatnessCore.scaledTangent g idx.2.1
    let w := FlatnessCore.scaledTangent g idx.2.2
    have hu : ∑ i, eval x (pderiv i F)*(u ∘ e.symm) i = 0 := by
      rw [← e.sum_comp]
      simpa only [Function.comp_apply,e.symm_apply_apply,← hge] using
        scaled_tangent_dot g idx.2.1
    have hw : ∑ i, eval x (pderiv i F)*(w ∘ e.symm) i = 0 := by
      rw [← e.sum_comp]
      simpa only [Function.comp_apply,e.symm_apply_apply,← hge] using
        scaled_tangent_dot g idx.2.2
    have H := LineFlatness.three_lines_tangent_zero F x v h2 hn hl h01 h02 h12
      (u ∘ e.symm) (w ∘ e.symm) hu hw
    simpa only [G,y,LineFlatness.hessian_rename,hc] using H
  · have hg : g = 0 := by
      ext i
      exact not_ne_iff.mp (fun h => hn ⟨e i,hge i ▸ h⟩)
    simp [hg,FlatnessCore.scaledTangent,LineFlatness.hessian]

variable {σ : Type*} [Fintype σ] [DecidableEq σ]
omit [Fintype σ] [DecidableEq σ] in
lemma natDegree_aeval_linear (x : σ → Polynomial K)
    (hx : ∀ i, (x i).natDegree ≤ 1) (F : MvPolynomial σ K) :
    (aeval x F).natDegree ≤ F.totalDegree := by
  conv_lhs => rw [F.as_sum]
  rw [map_sum]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro d hd
  rw [aeval_monomial]
  apply (Polynomial.natDegree_mul_le).trans
  simp only [Polynomial.algebraMap_apply,Polynomial.natDegree_C,zero_add]
  calc
    _ ≤ ∑ i ∈ d.support, (x i ^ d i).natDegree := Polynomial.natDegree_prod_le _ _
    _ ≤ ∑ i ∈ d.support, d i := by
      apply Finset.sum_le_sum
      intro i hi
      rw [Polynomial.natDegree_pow]
      simpa [Nat.mul_comm] using Nat.mul_le_mul_right (d i) (hx i)
    _ ≤ F.totalDegree := le_totalDegree hd
omit [Fintype σ] [DecidableEq σ] in

lemma restriction_degree (x v : σ → K) (F : MvPolynomial σ K) :
    (LineFlatness.restrictLine x v F).natDegree ≤ F.totalDegree := by
  apply natDegree_aeval_linear
  intro i
  exact (Polynomial.natDegree_add_le _ _).trans (max_le (by simp)
    ((Polynomial.natDegree_mul_le).trans (by simp)))
omit [Fintype σ] [DecidableEq σ] in

lemma restriction_eval (x v : σ → K) (F : MvPolynomial σ K) (t : K) :
    (LineFlatness.restrictLine x v F).eval t = eval (fun i => x i+v i*t) F := by
  induction F using MvPolynomial.induction_on with
  | C c => simp [LineFlatness.restrictLine]
  | add f g hf hg => simp_all [LineFlatness.restrictLine]
  | mul_X f i hf => simp_all [LineFlatness.restrictLine]
omit [Fintype σ] [DecidableEq σ] in

lemma restriction_zero_of_many (x v : σ → K) (F : MvPolynomial σ K)
    (S : Finset K) (hcard : F.totalDegree < S.card)
    (hzero : ∀ t ∈ S, eval (fun i => x i+v i*t) F = 0) :
    LineFlatness.restrictLine x v F = 0 := by
  by_contra hn
  have H : S.card ≤ (LineFlatness.restrictLine x v F).natDegree := by
    apply Polynomial.card_le_degree_of_subset_roots
    intro t ht
    exact (Polynomial.mem_roots hn).mpr ((restriction_eval x v F t).trans (hzero t ht))
  exact (not_lt_of_ge (H.trans (restriction_degree x v F))) hcard

theorem auxiliary_polynomial {p : ℕ} [CharP K p] [IsAlgClosed K]
    (F : MvPolynomial (Fin 3) K) (hF : F ≠ 0) (hdeg : F.totalDegree < p)
    (hs : Squarefree F) (h2 : (2 : K) ≠ 0)
    (hn : ∀ L : MvPolynomial (Fin 3) K, L ∣ F → L.totalDegree ≤ 1 → IsUnit L) :
    ∃ Q : MvPolynomial (Fin 3) K, IsRelPrime F Q ∧ Q.totalDegree ≤ 3*F.totalDegree ∧
      ∀ (x v : Fin 3 → K) (S : Finset K), 3*F.totalDegree < S.card →
        (∀ t ∈ S, ∃ w : Fin 3 → Fin 3 → K,
          (∀ i, LineFlatness.restrictLine (fun j => x j+v j*t) (w i) F = 0) ∧
          LinearIndependent K ![w 0,w 1] ∧ LinearIndependent K ![w 0,w 2] ∧
          LinearIndependent K ![w 1,w 2]) → LineFlatness.restrictLine x v Q = 0 := by
  obtain ⟨c,hc,hd⟩ := exists_coprime_flat_combination F hF hdeg hs hn
  refine ⟨∑ i, c i • flatFamily F i,hc,hd,?_⟩
  intro x v S hS hpoints
  apply restriction_zero_of_many x v _ S (hd.trans_lt hS)
  intro t ht
  obtain ⟨w,hw,h01,h02,h12⟩ := hpoints t ht
  simp only [map_sum,Algebra.smul_def,MvPolynomial.algebraMap_eq,map_mul,eval_C]
  apply sum_eq_zero
  intro i hi
  rw [family_zero_at_three_lines F _ w h2 hw h01 h02 h12 i,mul_zero]

end SharpLogRamsey.RichLinePolynomial

end

section

section

open scoped BigOperators nonZeroDivisors
open Polynomial Finset
namespace SharpLogRamsey.ParametricBezout

section Fraction
variable {R K : Type*} [CommRing R] [IsDomain R] [NormalizedGCDMonoid R]
  [Field K] [Algebra R K] [IsFractionRing R K]

lemma isCoprime_map_fraction {f g : R[X]} (h : IsRelPrime f g) :
    IsCoprime (f.map (algebraMap R K)) (g.map (algebraMap R K)) := by
  apply isRelPrime_iff_isCoprime.mp
  intro a haf hag
  have ha : a ≠ 0 := by
    intro hz
    rw [hz,zero_dvd_iff] at haf hag
    have hf : f = 0 := (Polynomial.map_injective _ (IsFractionRing.injective R K))
      (by simpa using haf)
    have hg : g = 0 := (Polynomial.map_injective _ (IsFractionRing.injective R K))
      (by simpa using hag)
    rcases h.ne_zero_or_ne_zero with H|H <;> contradiction
  let b : R[X] := IsLocalization.integerNormalization R⁰ a
  have hb : b.primPart.IsPrimitive := Polynomial.isPrimitive_primPart b
  have hab : b.primPart.map (algebraMap R K) ∣ a := by
    have H := Polynomial.map_dvd (algebraMap R K) (Polynomial.primPart_dvd b)
    obtain ⟨c,hc,hbmap⟩ := IsLocalization.integerNormalization_spec R⁰ a
    change b.map (algebraMap R K) = _ at hbmap
    rw [hbmap,Algebra.smul_def,Polynomial.algebraMap_apply] at H
    have hc0 : algebraMap R K c ≠ 0 := by
      intro he
      apply nonZeroDivisors.ne_zero hc
      apply IsFractionRing.injective R K
      simpa using he
    exact (IsUnit.dvd_mul_left (Polynomial.isUnit_C.mpr
      (isUnit_iff_ne_zero.mpr hc0))).mp H
  have hbf := hb.dvd_of_fraction_map_dvd_fraction_map (hab.trans haf)
  have hbg := hb.dvd_of_fraction_map_dvd_fraction_map (hab.trans hag)
  exact Polynomial.isUnit_or_eq_zero_of_isUnit_integerNormalization_primPart ha (h hbf hbg)

include K in
lemma resultant_ne_zero_of_isRelPrime {f g : R[X]} (h : IsRelPrime f g) :
    f.resultant g ≠ 0 := by
  have hc := isCoprime_map_fraction (K := K) h
  have H := Polynomial.resultant_ne_zero _ _ hc
  have hf := Polynomial.natDegree_map_eq_of_injective (IsFractionRing.injective R K) f
  have hg := Polynomial.natDegree_map_eq_of_injective (IsFractionRing.injective R K) g
  rw [hf,hg,Polynomial.resultant_map_map] at H
  exact fun he => H (by rw [he,map_zero])
end Fraction

variable {K : Type*} [CommRing K] [IsDomain K] [NormalizedGCDMonoid K]
omit [IsDomain K] [NormalizedGCDMonoid K] in

lemma natDegree_det_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι K[X]) (d : ι → ℕ)
    (h : ∀ i j, (M i j).natDegree ≤ d j) :
    M.det.natDegree ≤ ∑ j,d j := by
  rw [Matrix.det_apply]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro e he
  apply (Polynomial.natDegree_smul_le _ _).trans
  apply (Polynomial.natDegree_prod_le _ _).trans
  apply sum_le_sum
  intro i hi
  exact h (e i) i

omit [IsDomain K] [NormalizedGCDMonoid K] in

lemma resultant_degree_bound (f g : (K[X])[X]) (Df Dg : ℕ)
    (hf : ∀ i, (f.coeff i).natDegree ≤ Df)
    (hg : ∀ i, (g.coeff i).natDegree ≤ Dg) :
    (f.resultant g).natDegree ≤ f.natDegree*Dg+g.natDegree*Df := by
  calc
    _ ≤ ∑ j : Fin (f.natDegree+g.natDegree),
        j.addCases (fun _ => Dg) (fun _ => Df) := by
      apply natDegree_det_le
      intro i j
      refine Fin.addCases ?_ ?_ j
      · intro j
        simp only [Polynomial.sylvester,Matrix.of_apply,Fin.addCases_left]
        split_ifs <;> simp_all
      · intro j
        simp only [Polynomial.sylvester,Matrix.of_apply,Fin.addCases_right]
        split_ifs <;> simp_all
    _ = _ := by rw [Fin.sum_univ_add]; simp

omit [IsDomain K] [NormalizedGCDMonoid K] in

lemma resultant_eval_zero (f g : (K[X])[X]) (x y : K)
    (hf : (f.map (Polynomial.evalRingHom x)).eval y = 0)
    (hg : (g.map (Polynomial.evalRingHom x)).eval y = 0)
    (hdeg : f.natDegree ≠ 0 ∨ g.natDegree ≠ 0) :
    (f.resultant g).eval x = 0 := by
  obtain ⟨a,b,ha,hb,H⟩ := Polynomial.exists_mul_add_mul_eq_C_resultant f g le_rfl le_rfl hdeg
  have h := congrArg (fun p : (K[X])[X] => (p.map (Polynomial.evalRingHom x)).eval y) H
  simpa [hf,hg] using h.symm

lemma common_points_card_le (f g : (K[X])[X]) (Df Dg : ℕ)
    (hc : IsRelPrime f g)
    (hf : ∀ i, (f.coeff i).natDegree ≤ Df)
    (hg : ∀ i, (g.coeff i).natDegree ≤ Dg)
    (hdeg : f.natDegree ≠ 0 ∨ g.natDegree ≠ 0)
    (S : Finset (K × K)) (hinj : Set.InjOn Prod.fst (S : Set (K × K)))
    (hS : ∀ z ∈ S, (f.map (Polynomial.evalRingHom z.1)).eval z.2 = 0 ∧
      (g.map (Polynomial.evalRingHom z.1)).eval z.2 = 0) :
    S.card ≤ f.natDegree*Dg+g.natDegree*Df := by
  classical
  have hne : f.resultant g ≠ 0 :=
    resultant_ne_zero_of_isRelPrime (K := FractionRing K[X]) hc
  calc
    S.card = (S.image Prod.fst).card := (Finset.card_image_of_injOn hinj).symm
    _ ≤ (f.resultant g).natDegree := by
      apply Polynomial.card_le_degree_of_subset_roots
      intro x hx
      obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hx
      exact (Polynomial.mem_roots hne).mpr (resultant_eval_zero f g z.1 z.2
        (hS z hz).1 (hS z hz).2 hdeg)
    _ ≤ _ := resultant_degree_bound f g Df Dg hf hg
omit [NormalizedGCDMonoid K] in

lemma no_common_point_of_degree_zero (f g : (K[X])[X]) (hc : IsRelPrime f g)
    (hf : f.natDegree = 0) (hg : g.natDegree = 0) (x y : K)
    (hfx : (f.map (Polynomial.evalRingHom x)).eval y = 0)
    (hgx : (g.map (Polynomial.evalRingHom x)).eval y = 0) : False := by
  have hef := Polynomial.eq_C_of_natDegree_eq_zero hf
  have heg := Polynomial.eq_C_of_natDegree_eq_zero hg
  have hfr : (f.coeff 0).IsRoot x := by
    rw [hef] at hfx
    simpa only [Polynomial.map_C, Polynomial.eval_C, Polynomial.coe_evalRingHom, Polynomial.IsRoot] using hfx
  have hgr : (g.coeff 0).IsRoot x := by
    rw [heg] at hgx
    simpa only [Polynomial.map_C, Polynomial.eval_C, Polynomial.coe_evalRingHom, Polynomial.IsRoot] using hgx
  have hfd := map_dvd (Polynomial.C : K[X] →+* (K[X])[X])
    (Polynomial.dvd_iff_isRoot.mpr hfr)
  have hgd := map_dvd (Polynomial.C : K[X] →+* (K[X])[X])
    (Polynomial.dvd_iff_isRoot.mpr hgr)
  have hu : IsUnit (Polynomial.C (Polynomial.X-Polynomial.C x) : (K[X])[X]) := by
    apply hc
    · rwa [← hef] at hfd
    · rwa [← heg] at hgd
  exact Polynomial.not_isUnit_X_sub_C x (Polynomial.isUnit_C.mp hu)

theorem graph_branches_card_le (f g : (K[X])[X]) (Df Dg : ℕ)
    (hc : IsRelPrime f g)
    (hf : ∀ i, (f.coeff i).natDegree ≤ Df)
    (hg : ∀ i, (g.coeff i).natDegree ≤ Dg)
    (hfo : f.natDegree ≤ Df) (hgo : g.natDegree ≤ Dg)
    (S : Finset (K × K)) (hinj : Set.InjOn Prod.fst (S : Set (K × K)))
    (hS : ∀ z ∈ S, (f.map (Polynomial.evalRingHom z.1)).eval z.2 = 0 ∧
      (g.map (Polynomial.evalRingHom z.1)).eval z.2 = 0) :
    S.card ≤ 2*Df*Dg := by
  by_cases hdeg : f.natDegree ≠ 0 ∨ g.natDegree ≠ 0
  · apply (common_points_card_le f g Df Dg hc hf hg hdeg S hinj hS).trans
    nlinarith
  · push Not at hdeg
    have he : S = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro z hz
      exact no_common_point_of_degree_zero f g hc hdeg.1 hdeg.2 z.1 z.2
        (hS z hz).1 (hS z hz).2
    simp [he]

end SharpLogRamsey.ParametricBezout

end

section

namespace SharpLogRamsey.GenericCoordinates
open MvPolynomial Finset
open scoped BigOperators
variable {K : Type*} [Field K] [Infinite K]
noncomputable section

lemma exists_eval_ne_zero {σ : Type*} (F : MvPolynomial σ K) (hF : F ≠ 0) :
    ∃ x : σ → K, eval x F ≠ 0 := by
  by_contra! h
  apply hF
  exact MvPolynomial.funext (by simpa using h)

lemma exists_first (T : Finset (Fin 3 → K)) (hT : ∀ v ∈ T, v ≠ 0) :
    ∃ a b : K, ∀ v ∈ T, v 0+a*v 1+b*v 2 ≠ 0 := by
  classical
  let f (v : Fin 3 → K) : MvPolynomial (Fin 2) K :=
    C (v 0)+C (v 1)*X 0+C (v 2)*X 1
  have hf : ∀ v ∈ T, f v ≠ 0 := by
    intro v hv H
    have h0 := congrArg (eval (fun _ => (0:K))) H
    have h1 := congrArg (eval ![1,0]) H
    have h2 := congrArg (eval ![0,1]) H
    simp [f] at h0 h1 h2
    apply hT v hv
    ext i
    fin_cases i <;> simp_all
  obtain ⟨x,hx⟩ := exists_eval_ne_zero (∏ v ∈ T, f v) (Finset.prod_ne_zero_iff.mpr hf)
  refine ⟨x 0,x 1,?_⟩
  intro v hv H
  apply hx
  rw [map_prod]
  apply Finset.prod_eq_zero hv
  simp [f,H,mul_comm]

lemma exists_second (a b : K) (T : Finset (Fin 3 → K))
    (hT : ∀ v ∈ T, v ≠ 0)
    (hk : ∀ v ∈ T, v 0+a*v 1+b*v 2 = 0) :
    ∃ c : K, ∀ v ∈ T, v 1+c*v 2 ≠ 0 := by
  classical
  let f (v : Fin 3 → K) : MvPolynomial Unit K := C (v 1)+C (v 2)*X ()
  have hf : ∀ v ∈ T, f v ≠ 0 := by
    intro v hv H
    have h1 := congrArg (eval (fun _ => (0:K))) H
    have h2 := congrArg (eval (fun _ => (1:K))) H
    simp [f] at h1 h2
    have h0 := hk v hv
    apply hT v hv
    ext i
    fin_cases i <;> simp_all
  obtain ⟨x,hx⟩ := exists_eval_ne_zero (∏ v ∈ T, f v) (Finset.prod_ne_zero_iff.mpr hf)
  refine ⟨x (),?_⟩
  intro v hv H
  apply hx
  rw [map_prod]
  apply Finset.prod_eq_zero hv
  simp [f,H,mul_comm]

omit [Infinite K] in

lemma map_direction (t : (Fin 3 → K) →ₗ[K] K) (v : Fin 3 → K) (hv : t v ≠ 0) :
    t (direction t v) = 1 := by simp [direction,hv]
omit [Infinite K] in
lemma map_base (t : (Fin 3 → K) →ₗ[K] K) (x v : Fin 3 → K) (hv : t v ≠ 0) :
    t (base t x v) = 0 := by simp [base,map_direction t v hv]
omit [Infinite K] in

lemma line_normalize (t : (Fin 3 → K) →ₗ[K] K) (x v : Fin 3 → K) (hv : t v ≠ 0) :
    line (base t x v) (direction t v) = line x v := by
  ext y
  constructor
  · rintro ⟨r,rfl⟩
    refine ⟨(r-t x)*(t v)⁻¹,?_⟩
    ext i
    simp [base,direction]
    ring
  · rintro ⟨r,rfl⟩
    refine ⟨t x+r*t v,?_⟩
    ext i
    simp [base,direction]
    field_simp
    ; ring

theorem exists_separating_coordinates {ι : Type*} [Fintype ι]
    (x v : ι → Fin 3 → K) (hv : ∀ i, v i ≠ 0)
    (hd : Function.Injective (fun i => line (x i) (v i))) :
    ∃ a b c : K, (∀ i, first a b (v i) ≠ 0) ∧
      Function.Injective (fun i =>
        Polynomial.C ((shear a b c (base (first a b) (x i) (v i))) 1)+
        Polynomial.C ((shear a b c (direction (first a b) (v i))) 1)*Polynomial.X) := by
  classical
  obtain ⟨a,b,hab⟩ := exists_first (Finset.univ.image v) (by
    intro w hw
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hw
    exact hv i)
  have ht : ∀ i, first a b (v i) ≠ 0 := by
    intro i
    exact hab (v i) (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩)
  let u := fun i => direction (first a b) (v i)
  let z := fun i => base (first a b) (x i) (v i)
  have hdistinct : ∀ i j, i ≠ j → z i ≠ z j ∨ u i ≠ u j := by
    intro i j hij
    by_contra! H
    apply hij
    apply hd
    change line (x i) (v i) = line (x j) (v j)
    rw [← line_normalize (first a b) (x i) (v i) (ht i),
      ← line_normalize (first a b) (x j) (v j) (ht j)]
    exact congrArg₂ line H.1 H.2
  let I := {ij : ι × ι // ij.1 ≠ ij.2}
  let w : I → Fin 3 → K := fun ij =>
    if z ij.val.1 ≠ z ij.val.2 then z ij.val.1-z ij.val.2 else u ij.val.1-u ij.val.2
  have hw : ∀ i, w i ≠ 0 := by
    intro i
    change (if z i.val.1 ≠ z i.val.2 then z i.val.1-z i.val.2 else u i.val.1-u i.val.2) ≠ 0
    by_cases H : z i.val.1 ≠ z i.val.2
    · rw [ite_eq_left H]; exact sub_ne_zero.mpr H
    · rw [ite_eq_right H]; exact sub_ne_zero.mpr ((hdistinct _ _ i.property).resolve_left H)
  have hk : ∀ i, first a b (w i) = 0 := by
    intro i
    change first a b (if z i.val.1 ≠ z i.val.2 then z i.val.1-z i.val.2 else u i.val.1-u i.val.2) = 0
    by_cases H : z i.val.1 ≠ z i.val.2
    · rw [ite_eq_left H,map_sub,map_base _ _ _ (ht _),map_base _ _ _ (ht _),sub_self]
    · rw [ite_eq_right H,map_sub,map_direction _ _ (ht _),map_direction _ _ (ht _),sub_self]
  obtain ⟨c,hc⟩ := exists_second a b (Finset.univ.image w) (by
    intro q hq
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hq
    exact hw i) (by
    intro q hq
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hq
    exact hk i)
  refine ⟨a,b,c,ht,?_⟩
  intro i j H
  by_contra hij
  have h0 := congrArg (fun p : Polynomial K => p.coeff 0) H
  have h1 := congrArg (fun p : Polynomial K => p.coeff 1) H
  simp only [Polynomial.coeff_add,Polynomial.coeff_C,Polynomial.coeff_C_mul,
    Polynomial.coeff_X_zero,mul_zero,add_zero,Polynomial.coeff_X_one,mul_one,
    zero_add,ite_true,ite_false,Nat.one_ne_zero] at h0 h1
  have Hc := hc (w ⟨(i,j),hij⟩) (Finset.mem_image.mpr ⟨⟨(i,j),hij⟩,Finset.mem_univ _,rfl⟩)
  apply Hc
  change (if z i ≠ z j then z i-z j else u i-u j) 1+
    c*(if z i ≠ z j then z i-z j else u i-u j) 2 = 0
  by_cases Hz : z i ≠ z j
  · rw [ite_eq_left Hz]
    change z i 1+c*z i 2 = z j 1+c*z j 2 at h0
    simp only [Pi.sub_apply]
    linear_combination h0
  · rw [ite_eq_right Hz]
    change u i 1+c*u i 2 = u j 1+c*u j 2 at h1
    simp only [Pi.sub_apply]
    linear_combination h1

end
end SharpLogRamsey.GenericCoordinates

end

end
end
end

end OAI
end

section
-- module Solutions.OAIQ060_R5.SharpRamsey_Geometry_Triple
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Incidence bounds for rich lines and finite point configurations. -/

section
section
section
section
namespace SharpLogRamsey.PolynomialCoordinates
open MvPolynomial
variable {K : Type*} [Field K]
noncomputable section

lemma encode_natDegree (F : MvPolynomial (Fin 3) K) :
    (encode F).natDegree ≤ F.totalDegree := by
  simp only [encode,AlgEquiv.trans_apply,Polynomial.coe_mapAlgEquiv]
  rw [Polynomial.natDegree_map_eq_of_injective (AlgEquiv.injective _),natDegree_finSuccEquiv]
  exact (degreeOf_le_totalDegree _ _).trans (totalDegree_rename_le _ _)

lemma coeff_degree_le {n : ℕ} (F : MvPolynomial (Fin (n+1)) K) (i : ℕ) :
    ((finSuccEquiv K n F).coeff i).totalDegree ≤ F.totalDegree := by
  by_cases h : (finSuccEquiv K n F).coeff i = 0
  · simp [h]
  · exact (Nat.le_add_right _ _).trans (totalDegree_coeff_finSuccEquiv_add_le F i h)

lemma encode_coeff_natDegree (F : MvPolynomial (Fin 3) K) (i : ℕ) :
    ((encode F).coeff i).natDegree ≤ F.totalDegree := by
  simp only [encode,AlgEquiv.trans_apply,Polynomial.coe_mapAlgEquiv,Polynomial.coeff_map]
  change (Polynomial.map (uniqueAlgEquiv K (Fin 1)).toRingHom
    (finSuccEquiv K 1 (((finSuccEquiv K 2) ((renameEquiv K (Equiv.swap 0 2)) F)).coeff i))).natDegree ≤ F.totalDegree
  rw [Polynomial.natDegree_map_eq_of_injective (AlgEquiv.injective _),natDegree_finSuccEquiv]
  exact (degreeOf_le_totalDegree _ _).trans
    ((coeff_degree_le _ i).trans (totalDegree_rename_le _ _))

lemma totalDegree_aeval_linear {σ τ : Type*} (x : τ → MvPolynomial σ K)
    (hx : ∀ i, (x i).totalDegree ≤ 1) (F : MvPolynomial τ K) :
    (MvPolynomial.aeval x F).totalDegree ≤ F.totalDegree := by
  classical
  conv_lhs => rw [F.as_sum]
  rw [map_sum]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro d hd
  rw [MvPolynomial.aeval_monomial]
  apply le_trans (MvPolynomial.totalDegree_mul _ _)
  simp only [MvPolynomial.algebraMap_eq, MvPolynomial.totalDegree_C,zero_add]
  calc
    _ ≤ ∑ i ∈ d.support, (x i ^ d i).totalDegree := MvPolynomial.totalDegree_finsetProd _ _
    _ ≤ ∑ i ∈ d.support, d i := by
      apply Finset.sum_le_sum
      intro i hi
      apply (MvPolynomial.totalDegree_pow _ _).trans
      simpa [Nat.mul_comm] using Nat.mul_le_mul_right (d i) (hx i)
    _ ≤ F.totalDegree := MvPolynomial.le_totalDegree hd

lemma change_degree (a b c : K) (F : MvPolynomial (Fin 3) K) :
    (change a b c F).totalDegree ≤ F.totalDegree := by
  apply totalDegree_aeval_linear
  intro i
  fin_cases i
  · apply (totalDegree_add _ _).trans
    apply max_le
    · apply (totalDegree_sub _ _).trans
      apply max_le (by simp)
      exact (totalDegree_mul _ _).trans (by simp only [totalDegree_C,totalDegree_X]; omega)
    · exact (totalDegree_mul _ _).trans (by simp only [totalDegree_C,totalDegree_X]; omega)
  · apply (totalDegree_sub _ _).trans
    apply max_le (by simp)
    exact (totalDegree_mul _ _).trans (by simp only [totalDegree_C,totalDegree_X]; omega)
  · simp

lemma eval_change (a b c : K) (w : Fin 3 → K) (F : MvPolynomial (Fin 3) K) :
    eval w (change a b c F) =
      eval ![w 0-a*w 1+(a*c-b)*w 2,w 1-c*w 2,w 2] F := by
  change eval w (changeHom a b c F) = _
  induction F using MvPolynomial.induction_on with
  | C r => simp [changeHom]
  | add f g hf hg => simp only [map_add,hf,hg]
  | mul_X f i hf =>
    simp only [map_mul,hf]
    congr 1
    fin_cases i <;> simp [changeHom]

lemma eval_encode (y z : Polynomial K) (r : K) (F : MvPolynomial (Fin 3) K) :
    (((encode F).map (Polynomial.evalRingHom y)).eval z).eval r =
      eval ![r,y.eval r,z.eval r] F := by
  induction F using MvPolynomial.induction_on with
  | C a => simp
  | add f g hf hg => simp only [map_add,Polynomial.map_add,Polynomial.eval_add,hf,hg]
  | mul_X f i hf =>
    simp only [map_mul,Polynomial.map_mul,Polynomial.eval_mul,hf]
    congr 1
    fin_cases i <;> simp

end
end SharpLogRamsey.PolynomialCoordinates

end

namespace SharpLogRamsey.CommonLines
open GenericCoordinates PolynomialCoordinates
variable {K : Type*} [Field K] [Infinite K]
noncomputable section

lemma coprime_equiv {R S : Type*} [CommRing R] [CommRing S]
    (e : R ≃+* S) {F G : R} (h : IsRelPrime F G) : IsRelPrime (e F) (e G) := by
  intro a haf hag
  have hu := h (by simpa using map_dvd e.symm haf) (by simpa using map_dvd e.symm hag)
  simpa using hu.map e
omit [Infinite K] in

lemma eval_change_shear (a b c : K) (w : Fin 3 → K) (F : MvPolynomial (Fin 3) K) :
    MvPolynomial.eval (shear a b c w) (change a b c F) = MvPolynomial.eval w F := by
  rw [eval_change]
  apply congrArg (fun z : Fin 3 → K => MvPolynomial.eval z F)
  ext i
  fin_cases i <;> simp [shear] ; ring

lemma graph_zero (a b c : K) (x v : Fin 3 → K) (hv : first a b v ≠ 0)
    (F : MvPolynomial (Fin 3) K) (hF : ∀ r : K, MvPolynomial.eval (x+r • v) F = 0) :
    let U := direction (first a b) v
    let B := base (first a b) x v
    let Y := Polynomial.C ((shear a b c B) 1)+Polynomial.C ((shear a b c U) 1)*Polynomial.X
    let Z := Polynomial.C ((shear a b c B) 2)+Polynomial.C ((shear a b c U) 2)*Polynomial.X
    ((encode (change a b c F)).map (Polynomial.evalRingHom Y)).eval Z = 0 := by
  dsimp only
  apply Polynomial.funext
  intro r
  rw [Polynomial.eval_zero,eval_encode]
  let U := direction (first a b) v
  let B := base (first a b) x v
  have h0 : (shear a b c (B+r • U)) 0 = r := by
    change first a b (B+r • U) = r
    rw [map_add,map_smul,map_base _ _ _ hv,map_direction _ _ hv]
    simp
  have he : ![r,
      (Polynomial.C ((shear a b c B) 1)+Polynomial.C ((shear a b c U) 1)*Polynomial.X).eval r,
      (Polynomial.C ((shear a b c B) 2)+Polynomial.C ((shear a b c U) 2)*Polynomial.X).eval r] =
      shear a b c (B+r • U) := by
    ext i
    fin_cases i
    · exact h0.symm
    · change (Polynomial.C ((shear a b c B) 1)+Polynomial.C ((shear a b c U) 1)*Polynomial.X).eval r =
        (shear a b c (B+r • U)) 1
      simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
        map_add, map_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_comm]
    · change (Polynomial.C ((shear a b c B) 2)+Polynomial.C ((shear a b c U) 2)*Polynomial.X).eval r =
        (shear a b c (B+r • U)) 2
      simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
        map_add, map_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_comm]
  rw [he,eval_change_shear]
  have hp : B+r • U ∈ line x v := by
    rw [← line_normalize (first a b) x v hv]
    exact ⟨r,rfl⟩
  obtain ⟨s,hs⟩ := hp
  rw [← hs]
  exact hF s

theorem card_le {ι : Type*} [Fintype ι]
    (F G : MvPolynomial (Fin 3) K) (hc : IsRelPrime F G)
    (x v : ι → Fin 3 → K) (hv : ∀ i, v i ≠ 0)
    (hd : Function.Injective (fun i => line (x i) (v i)))
    (hF : ∀ i (r : K), MvPolynomial.eval (x i+r • v i) F = 0)
    (hG : ∀ i (r : K), MvPolynomial.eval (x i+r • v i) G = 0) :
    Fintype.card ι ≤ 2*F.totalDegree*G.totalDegree := by
  classical
  obtain ⟨a,b,c,ht,hsep⟩ := exists_separating_coordinates x v hv hd
  let Y := fun i => Polynomial.C ((shear a b c (base (first a b) (x i) (v i))) 1)+
    Polynomial.C ((shear a b c (direction (first a b) (v i))) 1)*Polynomial.X
  let Z := fun i => Polynomial.C ((shear a b c (base (first a b) (x i) (v i))) 2)+
    Polynomial.C ((shear a b c (direction (first a b) (v i))) 2)*Polynomial.X
  let e : MvPolynomial (Fin 3) K ≃ₐ[K] Polynomial (Polynomial (Polynomial K)) :=
    (change a b c).trans (encode (K := K))
  let S := Finset.univ.image (fun i => (Y i,Z i))
  have hpair : Function.Injective (fun i => (Y i,Z i)) := by
    intro i j H
    exact hsep (congrArg Prod.fst H)
  have hcard : S.card = Fintype.card ι := by simp [S,Finset.card_image_of_injective _ hpair]
  rw [← hcard]
  apply ParametricBezout.graph_branches_card_le (e F) (e G) F.totalDegree G.totalDegree
  · exact coprime_equiv (S := Polynomial (Polynomial (Polynomial K))) e.toRingEquiv hc
  · intro i
    exact (encode_coeff_natDegree (change a b c F) i).trans (change_degree a b c F)
  · intro i
    exact (encode_coeff_natDegree (change a b c G) i).trans (change_degree a b c G)
  · exact (encode_natDegree (change a b c F)).trans (change_degree a b c F)
  · exact (encode_natDegree (change a b c G)).trans (change_degree a b c G)
  · intro y hy z hz H
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hz
    exact congrArg (fun i => (Y i,Z i)) (hsep H)
  · intro z hz
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hz
    exact ⟨graph_zero a b c (x i) (v i) (ht i) F (hF i),
      graph_zero a b c (x i) (v i) (ht i) G (hG i)⟩

end
end SharpLogRamsey.CommonLines

end

section

namespace SharpLogRamsey.AffineIncidence
open Finset
open scoped BigOperators
variable {K : Type*} [Field K] {ι : Type*} [Fintype ι]
noncomputable section

lemma parametrization_injective (x v : Fin 3 → K) (hv : v ≠ 0) :
    Function.Injective (fun r : K => x+r • v) := by
  intro a b H
  exact (smul_left_injective K hv) (add_left_cancel H)

lemma rebase (x v y : Fin 3 → K) (hy : y ∈ carrier x v) :
    carrier y v = carrier x v := by
  obtain ⟨s,rfl⟩ := hy
  ext z
  constructor
  · rintro ⟨r,rfl⟩
    refine ⟨s+r,?_⟩
    simp only [add_smul]
    abel
  · rintro ⟨r,rfl⟩
    refine ⟨r-s,?_⟩
    simp only [sub_smul]
    abel

lemma scale (x v : Fin 3 → K) (a : K) (ha : a ≠ 0) :
    carrier x (a • v) = carrier x v := by
  ext z
  constructor
  · rintro ⟨r,rfl⟩
    exact ⟨r*a,by simp [mul_smul]⟩
  · rintro ⟨r,rfl⟩
    exact ⟨r/a,by simp [smul_smul,ha]⟩
omit [Fintype ι] in

lemma independent_at_intersection (x v : ι → Fin 3 → K)
    (hv : ∀ i, v i ≠ 0) (hd : Function.Injective (fun i => carrier (x i) (v i)))
    (i j : ι) (hij : i ≠ j) (y : Fin 3 → K)
    (hi : y ∈ carrier (x i) (v i)) (hj : y ∈ carrier (x j) (v j)) :
    LinearIndependent K ![v i,v j] := by
  rw [linearIndependent_fin2]
  refine ⟨hv j,?_⟩
  intro a ha
  have ha0 : a ≠ 0 := by intro h; subst a; simp only [zero_smul] at ha; exact hv i ha.symm
  apply hij
  apply hd
  change carrier (x i) (v i) = carrier (x j) (v j)
  change a • v j = v i at ha
  rw [← rebase (x i) (v i) y hi,← rebase (x j) (v j) y hj,← ha,scale y (v j) a ha0]
omit [Fintype ι] in

lemma intersection_subsingleton (x v : ι → Fin 3 → K)
    (hv : ∀ i, v i ≠ 0) (hd : Function.Injective (fun i => carrier (x i) (v i)))
    (i j : ι) (hij : i ≠ j) :
    (carrier (x i) (v i) ∩ carrier (x j) (v j)).Subsingleton := by
  intro y hy z hz
  have hlin := independent_at_intersection x v hv hd i j hij y hy.1 hy.2
  have hzi : z ∈ carrier y (v i) := by rw [rebase (x i) (v i) y hy.1]; exact hz.1
  have hzj : z ∈ carrier y (v j) := by rw [rebase (x j) (v j) y hy.2]; exact hz.2
  obtain ⟨a,ha⟩ := hzi
  obtain ⟨b,hb⟩ := hzj
  have he : a • v i = b • v j := add_left_cancel (ha.trans hb.symm)
  have hc := hlin.eq_coords_of_eq (f := ![a,0]) (g := ![0,b])
    (by simpa using he) 0
  have ha0 : a = 0 := hc
  simpa [ha0] using ha
omit [Fintype ι] in

lemma points_intersection_le [DecidableEq K] (x v : ι → Fin 3 → K)
    (hv : ∀ i, v i ≠ 0) (hd : Function.Injective (fun i => carrier (x i) (v i)))
    (A : ι → Finset (Fin 3 → K)) (hA : ∀ i, (A i : Set _) ⊆ carrier (x i) (v i))
    (i j : ι) (hij : i ≠ j) : (A i ∩ A j).card ≤ 1 := by
  apply card_le_one.mpr
  intro y hy z hz
  exact intersection_subsingleton x v hv hd i j hij
    ⟨hA i (mem_inter.mp hy).1,hA j (mem_inter.mp hy).2⟩
    ⟨hA i (mem_inter.mp hz).1,hA j (mem_inter.mp hz).2⟩

variable (x v : ι → Fin 3 → K)

lemma split_points (S : Finset (Fin 3 → K)) (i : ι) :
    (richPoints x v S i).card+(poorPoints x v S i).card = (onLine x v S i).card := by
  classical
  simpa [richPoints,poorPoints,not_lt] using
    card_filter_add_card_filter_not (s := onLine x v S i) (p := fun y => 2 < (pencil x v y).card)

lemma poor_total (S : Finset (Fin 3 → K)) :
    (∑ i, (poorPoints x v S i).card) ≤ 2*S.card := by
  classical
  have he : (∑ i, (poorPoints x v S i).card) =
      ∑ y ∈ S, if (pencil x v y).card ≤ 2 then (pencil x v y).card else 0 := by
    simp only [poorPoints,onLine,filter_filter]
    simp only [card_filter]
    rw [sum_comm]
    apply sum_congr rfl
    intro y hy
    by_cases H : (pencil x v y).card ≤ 2
    · simp only [H,and_true,ite_true]
      rw [show (pencil x v y).card = ∑ i, if y ∈ carrier (x i) (v i) then 1 else 0 by
        simp only [pencil,card_filter]]
    · simp only [H,and_false,ite_false,sum_const_zero]
  rw [he]
  calc
    _ ≤ ∑ _y ∈ S, 2 := by
      apply sum_le_sum
      intro y hy
      split_ifs with H
      · exact H
      · omega
    _ = 2*S.card := by simp [Nat.mul_comm]

theorem pruning_bound (S : Finset (Fin 3 → K)) (M D : ℕ)
    (hM : ∀ i, M ≤ (onLine x v S i).card) :
    let bad := Finset.univ.filter (fun i => (richPoints x v S i).card ≤ D)
    bad.card*(M-D) ≤ 2*S.card := by
  classical
  dsimp only
  calc
    _ = ∑ i ∈ univ.filter (fun i => (richPoints x v S i).card ≤ D), (M-D) := by simp
    _ ≤ ∑ i ∈ univ.filter (fun i => (richPoints x v S i).card ≤ D), (poorPoints x v S i).card := by
      apply sum_le_sum
      intro i hi
      have h := (mem_filter.mp hi).2
      have hs := split_points x v S i
      have hm := hM i
      omega
    _ ≤ ∑ i, (poorPoints x v S i).card := sum_le_sum_of_subset (filter_subset _ _)
    _ ≤ 2*S.card := poor_total x v S

end
end SharpLogRamsey.AffineIncidence

end

namespace SharpLogRamsey.NonplaneRichLines
open Finset MvPolynomial
open AffineIncidence
variable {K : Type*} [Field K] [Infinite K]
noncomputable section
omit [Infinite K] in

lemma eval_of_restrict_zero (x v : Fin 3 → K) (F : MvPolynomial (Fin 3) K)
    (h : LineFlatness.restrictLine x v F = 0) (y : Fin 3 → K)
    (hy : y ∈ carrier x v) : eval y F = 0 := by
  obtain ⟨t,rfl⟩ := hy
  have H := congrArg (fun p : Polynomial K => p.eval t) h
  rw [RichLinePolynomial.restriction_eval] at H
  have he : (fun i => x i+v i*t) = x+t • v := by ext i; simp [mul_comm]
  simpa only [he,Polynomial.eval_zero] using H

lemma restrict_zero_rebase (x v y : Fin 3 → K) (F : MvPolynomial (Fin 3) K)
    (h : LineFlatness.restrictLine x v F = 0) (hy : y ∈ carrier x v) :
    LineFlatness.restrictLine y v F = 0 := by
  apply Polynomial.funext
  intro r
  rw [RichLinePolynomial.restriction_eval,Polynomial.eval_zero]
  apply eval_of_restrict_zero x v F h
  rw [← rebase x v y hy]
  exact ⟨r,by ext i; simp [mul_comm]⟩

variable {ι : Type*} [Fintype ι]

lemma three_lines_at_rich (F : MvPolynomial (Fin 3) K)
    (x v : ι → Fin 3 → K) (hv : ∀ i, v i ≠ 0)
    (hd : Function.Injective (fun i => carrier (x i) (v i)))
    (hF : ∀ i, LineFlatness.restrictLine (x i) (v i) F = 0)
    (y : Fin 3 → K) (hy : 2 < (pencil x v y).card) :
    ∃ w : Fin 3 → Fin 3 → K,
      (∀ i, LineFlatness.restrictLine y (w i) F = 0) ∧
      LinearIndependent K ![w 0,w 1] ∧ LinearIndependent K ![w 0,w 2] ∧
      LinearIndependent K ![w 1,w 2] := by
  classical
  obtain ⟨a,b,c,ha,hb,hc,hab,hac,hbc⟩ := two_lt_card_iff.mp hy
  have ha' : y ∈ carrier (x a) (v a) := (mem_filter.mp ha).2
  have hb' : y ∈ carrier (x b) (v b) := (mem_filter.mp hb).2
  have hc' : y ∈ carrier (x c) (v c) := (mem_filter.mp hc).2
  refine ⟨![v a,v b,v c],?_,?_,?_,?_⟩
  · intro i
    fin_cases i
    · exact restrict_zero_rebase (x a) (v a) y F (hF a) ha'
    · exact restrict_zero_rebase (x b) (v b) y F (hF b) hb'
    · exact restrict_zero_rebase (x c) (v c) y F (hF c) hc'
  · exact independent_at_intersection x v hv hd a b hab y ha' hb'
  · exact independent_at_intersection x v hv hd a c hac y ha' hc'
  · exact independent_at_intersection x v hv hd b c hbc y hb' hc'
omit [Infinite K] in

lemma many_parameters (x v : ι → Fin 3 → K) (hv : ∀ i, v i ≠ 0)
    (S : Finset (Fin 3 → K)) (i : ι) :
    ∃ T : Finset K, T.card = (richPoints x v S i).card ∧
      ∀ t ∈ T, 2 < (pencil x v (fun j => x i j+v i j*t)).card := by
  classical
  let f : K → Fin 3 → K := fun t => x i+t • v i
  let T := (richPoints x v S i).preimage f (parametrization_injective _ _ (hv i)).injOn
  refine ⟨T,?_,?_⟩
  · rw [card_preimage]
    congr 1
    apply filter_eq_self.mpr
    intro y hy
    exact (mem_filter.mp (mem_filter.mp hy).1).2
  · intro t ht
    have H := (mem_filter.mp (mem_preimage.mp ht)).2
    have he : f t = (fun j => x i j+v i j*t) := by ext j; simp [f,mul_comm]
    simpa only [he] using H

end
end SharpLogRamsey.NonplaneRichLines
end
end

end OAI
end

section
-- module Solutions.OAIQ060_R5.SharpRamsey_Geometry_Card
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Incidence bounds for rich lines and finite point configurations. -/

section
section
namespace SharpLogRamsey.NonplaneRichLines
open Finset MvPolynomial
open AffineIncidence
variable {K : Type*} [Field K] [Infinite K]
noncomputable section
variable {ι : Type*} [Fintype ι]
theorem card_le {p : ℕ} [CharP K p] [IsAlgClosed K]
    (F : MvPolynomial (Fin 3) K) (hF : F ≠ 0) (hdeg : F.totalDegree < p)
    (hs : Squarefree F) (h2 : (2 : K) ≠ 0)
    (hn : ∀ L : MvPolynomial (Fin 3) K, L ∣ F → L.totalDegree ≤ 1 → IsUnit L)
    (x v : ι → Fin 3 → K) (hv : ∀ i, v i ≠ 0)
    (hd : Function.Injective (fun i => carrier (x i) (v i)))
    (hzero : ∀ i, LineFlatness.restrictLine (x i) (v i) F = 0)
    (S : Finset (Fin 3 → K)) (M : ℕ) (hM : ∀ i, M ≤ (onLine x v S i).card)
    (hMD : 3*F.totalDegree < M) :
    Fintype.card ι ≤ 2*S.card/(M-3*F.totalDegree)+6*F.totalDegree^2 := by
  classical
  obtain ⟨Q,hQ,hQD,hQr⟩ := RichLinePolynomial.auxiliary_polynomial F hF hdeg hs h2 hn
  let bad := univ.filter (fun i => (richPoints x v S i).card ≤ 3*F.totalDegree)
  let good := univ.filter (fun i => 3*F.totalDegree < (richPoints x v S i).card)
  have hb : bad.card ≤ 2*S.card/(M-3*F.totalDegree) := by
    apply (Nat.le_div_iff_mul_le (by omega)).mpr
    exact pruning_bound x v S M (3*F.totalDegree) hM
  have hgood : ∀ i ∈ good, LineFlatness.restrictLine (x i) (v i) Q = 0 := by
    intro i hi
    obtain ⟨T,hcard,hT⟩ := many_parameters x v hv S i
    apply hQr (x i) (v i) T (by rw [hcard]; exact (mem_filter.mp hi).2)
    intro t ht
    exact three_lines_at_rich F x v hv hd hzero _ (hT t ht)
  have hg : good.card ≤ 6*F.totalDegree^2 := by
    have H := CommonLines.card_le F Q hQ (fun i : good => x i) (fun i : good => v i)
      (fun i => hv i) (fun i j H => Subtype.ext (hd H))
      (fun i t => eval_of_restrict_zero _ _ F (hzero i) _ ⟨t,rfl⟩)
      (fun i t => eval_of_restrict_zero _ _ Q (hgood i i.property) _ ⟨t,rfl⟩)
    have H' : good.card ≤ 2*F.totalDegree*Q.totalDegree := by simpa using H
    calc
      _ ≤ 2*F.totalDegree*Q.totalDegree := H'
      _ ≤ 2*F.totalDegree*(3*F.totalDegree) := Nat.mul_le_mul_left _ hQD
      _ = 6*F.totalDegree^2 := by ring
  have hsplit : bad.card+good.card = Fintype.card ι := by
    simpa only [bad,good,not_le,card_univ] using
      card_filter_add_card_filter_not (s := univ) (p := fun i => (richPoints x v S i).card ≤ 3*F.totalDegree)
  omega

end
end SharpLogRamsey.NonplaneRichLines

section

namespace SharpLogRamsey.PlaneDecomposition
open MvPolynomial
variable {K : Type*} [Field K]
noncomputable section

lemma unit_of_degree_zero (F : MvPolynomial (Fin 3) K) (hF : F ≠ 0)
    (h : F.totalDegree = 0) : IsUnit F := by
  have he := totalDegree_eq_zero_iff_eq_C.mp h
  have hc : F.coeff 0 ≠ 0 := by
    intro H
    apply hF
    rw [he,H,map_zero]
  rw [he]
  exact (isUnit_iff_ne_zero.mpr hc).map C

theorem exists_decomposition (F : MvPolynomial (Fin 3) K) (hF : F ≠ 0)
    (hs : Squarefree F) :
    ∃ (planes : List (MvPolynomial (Fin 3) K)) (G : MvPolynomial (Fin 3) K),
      G ≠ 0 ∧ Squarefree G ∧ F = planes.prod*G ∧
      (∀ L ∈ planes, L.totalDegree = 1) ∧
      planes.Pairwise IsRelPrime ∧
      (∀ L ∈ planes, L ∣ F) ∧
      (∀ L : MvPolynomial (Fin 3) K, L ∣ G → L.totalDegree ≤ 1 → IsUnit L) ∧
      planes.length+G.totalDegree = F.totalDegree := by
  classical
  suffices H : ∀ n (F : MvPolynomial (Fin 3) K), F.totalDegree = n → F ≠ 0 → Squarefree F →
    ∃ (planes : List (MvPolynomial (Fin 3) K)) (G : MvPolynomial (Fin 3) K),
      G ≠ 0 ∧ Squarefree G ∧ F = planes.prod*G ∧
      (∀ L ∈ planes, L.totalDegree = 1) ∧ planes.Pairwise IsRelPrime ∧
      (∀ L ∈ planes, L ∣ F) ∧
      (∀ L : MvPolynomial (Fin 3) K, L ∣ G → L.totalDegree ≤ 1 → IsUnit L) ∧
      planes.length+G.totalDegree = F.totalDegree by
    exact H F.totalDegree F rfl hF hs
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro F hn hF hs
    by_cases hno : ∀ L : MvPolynomial (Fin 3) K, L ∣ F → L.totalDegree ≤ 1 → IsUnit L
    · exact ⟨[],F,hF,hs,by simp,by simp,by simp,by simp,hno,by simp⟩
    push Not at hno
    obtain ⟨L,hLF,hd,hnu⟩ := hno
    have hL : L ≠ 0 := ne_zero_of_dvd_ne_zero hF hLF
    have hdL : L.totalDegree = 1 := by
      have hn0 : L.totalDegree ≠ 0 := fun h => hnu (unit_of_degree_zero L hL h)
      omega
    obtain ⟨A,hFA⟩ := hLF
    have hA : A ≠ 0 := by
      intro H
      apply hF
      rw [hFA,H,mul_zero]
    have hde : F.totalDegree = 1+A.totalDegree := by
      rw [hFA,totalDegree_mul_of_isDomain hL hA,hdL]
    have hAl : A.totalDegree < n := by omega
    have hsq := squarefree_mul_iff.mp (hFA ▸ hs)
    obtain ⟨planes,G,hG,hGs,hAG,hplanes,hpair,hdiv,hng,hdeg⟩ :=
      ih A.totalDegree hAl A rfl hA hsq.2.2
    refine ⟨L::planes,G,hG,hGs,?_,?_,?_,?_,hng,?_⟩
    · simp only [List.prod_cons]
      rw [mul_assoc,← hAG,← hFA]
    · intro J hJ
      obtain rfl | hJ := List.mem_cons.mp hJ
      · exact hdL
      · exact hplanes J hJ
    · apply List.pairwise_cons.mpr
      exact ⟨fun J hJ => hsq.1.of_dvd_right (hdiv J hJ),hpair⟩
    · intro J hJ
      obtain rfl | hJ := List.mem_cons.mp hJ
      · exact ⟨A,hFA⟩
      · exact (hdiv J hJ).trans (hFA ▸ dvd_mul_left A L)
    · simp only [List.length_cons]
      omega

end
end SharpLogRamsey.PlaneDecomposition

end

section

namespace SharpLogRamsey.PlaneCount
open Finset
open scoped BigOperators
variable {ι X : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq X]
noncomputable section
omit [DecidableEq ι] in

lemma incidence_sum (A : ι → Finset X) (U : Finset X) (hU : ∀ i, A i ⊆ U) :
    (∑ x ∈ U, (univ.filter (fun i => x ∈ A i)).card) = ∑ i, (A i).card := by
  classical
  simp only [card_filter]
  rw [sum_comm]
  apply sum_congr rfl
  intro i hi
  have H : U.filter (fun x => x ∈ A i) = A i := by
    ext x
    simp only [mem_filter]
    exact ⟨fun h => h.2,fun h => ⟨hU i h,h⟩⟩
  rw [← card_filter,H]
omit [DecidableEq ι] in

lemma incidence_sq_sum (A : ι → Finset X) (U : Finset X) (hU : ∀ i, A i ⊆ U) :
    (∑ x ∈ U, (univ.filter (fun i => x ∈ A i)).card^2) =
      ∑ i, ∑ j, (A i ∩ A j).card := by
  classical
  have he (x : X) : (univ.filter (fun i => x ∈ A i)).card^2 =
      ∑ i, ∑ j, if x ∈ A i ∧ x ∈ A j then (1:ℕ) else 0 := by
    simp only [card_filter,pow_two,sum_mul,mul_sum]
    apply sum_congr rfl
    intro i hi
    apply sum_congr rfl
    intro j hj
    by_cases H : x ∈ A i <;> by_cases H' : x ∈ A j <;> simp [H,H']
  simp_rw [he]
  rw [sum_comm]
  apply sum_congr rfl
  intro i hi
  rw [sum_comm]
  apply sum_congr rfl
  intro j hj
  have H : U.filter (fun x => x ∈ A i ∧ x ∈ A j) = A i ∩ A j := by
    ext x
    simp only [mem_filter,mem_inter]
    exact ⟨fun h => h.2, fun h => ⟨hU i h.1,h⟩⟩
  rw [← card_filter,H]

theorem card_mul_le (A : ι → Finset X) (U : Finset X) (M K : ℕ)
    (hU : ∀ i, A i ⊆ U) (hM : ∀ i, (A i).card = M)
    (hi : ∀ i j, i ≠ j → (A i ∩ A j).card ≤ 1)
    (hK : U.card ≤ K) (hMK : 2*K ≤ M^2) (hM0 : 0 < M) :
    Fintype.card ι*M ≤ 2*K := by
  classical
  let u := Fintype.card ι
  have hs : (∑ x ∈ U, (univ.filter (fun i => x ∈ A i)).card) = u*M := by
    rw [incidence_sum A U hU]
    simp [hM,u]
  have hs2 : (∑ x ∈ U, (univ.filter (fun i => x ∈ A i)).card^2) ≤ u*(M+u) := by
    rw [incidence_sq_sum A U hU]
    calc
      _ ≤ ∑ i : ι, ∑ j : ι, ((if i = j then M else 0)+1) := by
        apply sum_le_sum; intro i _
        apply sum_le_sum; intro j _
        by_cases H : i = j
        · subst j; simp [hM]
        · simpa [H] using (hi i j H)
      _ = u*(M+u) := by simp [u,sum_add_distrib]
  have hcs := sq_sum_le_card_mul_sum_sq (s := U)
    (f := fun x => (univ.filter (fun i => x ∈ A i)).card)
  rw [hs] at hcs
  have H : (u*M)^2 ≤ K*(u*(M+u)) := hcs.trans (Nat.mul_le_mul hK hs2)
  by_cases hu : u = 0
  · change u*M ≤ 2*K
    simp [hu]
  have hu0 : 0 < u := Nat.pos_of_ne_zero hu
  have hcancel : u*M^2 ≤ K*(M+u) := by
    apply Nat.le_of_mul_le_mul_left (c := u)
    calc
      u*(u*M^2) = (u*M)^2 := by ring
      _ ≤ K*(u*(M+u)) := H
      _ = u*(K*(M+u)) := by ring
    exact hu0
  have hmid : u*M^2 ≤ 2*K*M := by nlinarith [Nat.mul_le_mul_left u hMK]
  change u*M ≤ 2*K
  apply Nat.le_of_mul_le_mul_right (c := M)
  · nlinarith
  · exact hM0

lemma exclusive_card (A : ι → Finset X) (i : ι)
    (hi : ∀ j, i ≠ j → (A i ∩ A j).card ≤ 1) :
    (A i).card ≤ (A i \ (univ.erase i).biUnion A).card+Fintype.card ι := by
  classical
  have he : A i ∩ (univ.erase i).biUnion A =
      (univ.erase i).biUnion (fun j => A i ∩ A j) := by
    ext x
    simp only [mem_inter,mem_biUnion]
    aesop
  have h : (A i ∩ (univ.erase i).biUnion A).card ≤ Fintype.card ι := by
    rw [he]
    calc
      _ ≤ ∑ j ∈ univ.erase i, (A i ∩ A j).card := card_biUnion_le
      _ ≤ ∑ _j ∈ univ.erase i, 1 := by
        apply sum_le_sum
        intro j hj
        exact hi j (mem_erase.mp hj).1.symm
      _ ≤ Fintype.card ι := by simp
  have hs := card_sdiff_add_card_inter (A i) ((univ.erase i).biUnion A)
  omega

lemma exclusive_disjoint (A : ι → Finset X) :
    (↑(univ : Finset ι) : Set ι).PairwiseDisjoint (fun i => A i \ (univ.erase i).biUnion A) := by
  classical
  intro i hi j hj hij
  apply disjoint_left.mpr
  intro x hxi hxj
  have hxi' := mem_sdiff.mp hxi
  have hxj' := mem_sdiff.mp hxj
  apply hxi'.2
  apply mem_biUnion.mpr
  exact ⟨j,mem_erase.mpr ⟨hij.symm,mem_univ j⟩,hxj'.1⟩

theorem union_lower (A : ι → Finset X) (M : ℕ)
    (hM : ∀ i, M ≤ (A i).card)
    (hi : ∀ i j, i ≠ j → (A i ∩ A j).card ≤ 1) :
    Fintype.card ι*(M-Fintype.card ι) ≤ (univ.biUnion A).card := by
  classical
  let E := fun i => A i \ (univ.erase i).biUnion A
  calc
    _ = ∑ _i : ι, (M-Fintype.card ι) := by simp
    _ ≤ ∑ i, (E i).card := by
      apply sum_le_sum
      intro i _
      have H := exclusive_card A i (hi i)
      have hm := hM i
      dsimp [E]
      omega
    _ = (univ.biUnion E).card := (card_biUnion (exclusive_disjoint A)).symm
    _ ≤ (univ.biUnion A).card := by
      apply card_le_card
      intro x hx
      obtain ⟨i,hi,hx⟩ := mem_biUnion.mp hx
      exact mem_biUnion.mpr ⟨i,hi,(mem_sdiff.mp hx).1⟩

end
end SharpLogRamsey.PlaneCount

namespace SharpLogRamsey.SinglePlaneCount
open Finset
open scoped BigOperators
variable {κ ι X : Type*} [Fintype κ] [Fintype ι] [DecidableEq X]
noncomputable section

theorem card_mul_le (A : ι → Finset X) (P : κ → Finset X) (owner : ι → κ)
    (U : Finset X) (M K : ℕ) (hM0 : 0 < M)
    (hM : ∀ i, (A i).card = M)
    (hAU : ∀ i, A i ⊆ P (owner i)) (hPU : ∀ j, P j ⊆ U)
    (hcap : ∀ j, (P j).card ≤ K)
    (hcross : ∀ i j, j ≠ owner i → (A i ∩ P j).card ≤ 1)
    (hpair : ∀ i j, i ≠ j → (A i ∩ A j).card ≤ 1)
    (hKM : 8*K ≤ M^2) (hDM : 4*Fintype.card κ ≤ M) :
    Fintype.card ι*M ≤ 2*U.card := by
  classical
  let D := Fintype.card κ
  let Region (j : κ) := P j \ (univ.erase j).biUnion P
  let u (j : κ) := Fintype.card {i : ι // owner i = j}
  have hu (j : κ) : 4*u j ≤ M := by
    have H := PlaneCount.card_mul_le (fun i : {i : ι // owner i = j} => A i.val)
      (P j) M K (by intro i; simpa [i.property] using hAU i.val)
      (fun i => hM i.val) (fun i k hik => hpair i.val k.val (by intro he; exact hik (Subtype.ext he)))
      (hcap j) (by omega) hM0
    change u j*M ≤ 2*K at H
    apply Nat.le_of_mul_le_mul_right (c := M)
    · nlinarith
    · exact hM0
  have hlocal (j : κ) : u j*M ≤ 2*(Region j).card := by
    let E : {i : ι // owner i = j} → Finset X := fun i => A i.val \ (univ.erase j).biUnion P
    have hEc (i : {i : ι // owner i = j}) : M-D ≤ (E i).card := by
      have he : A i.val ∩ (univ.erase j).biUnion P =
          (univ.erase j).biUnion (fun k => A i.val ∩ P k) := by
        ext a
        simp only [mem_inter,mem_biUnion]
        aesop
      have H : (A i.val ∩ (univ.erase j).biUnion P).card ≤ D := by
        rw [he]
        calc
          _ ≤ ∑ k ∈ univ.erase j, (A i.val ∩ P k).card := card_biUnion_le
          _ ≤ ∑ _k ∈ univ.erase j, 1 := by
            apply sum_le_sum
            intro k hk
            apply hcross
            simpa [i.property] using (mem_erase.mp hk).1
          _ ≤ D := by simp [D]
      have H' := card_sdiff_add_card_inter (A i.val) ((univ.erase j).biUnion P)
      rw [hM] at H'
      change M-D ≤ (A i.val \ (univ.erase j).biUnion P).card
      omega
    have hE (i : {i : ι // owner i = j}) : E i ⊆ Region j := by
      intro a ha
      obtain ⟨ha,hn⟩ := mem_sdiff.mp ha
      apply mem_sdiff.mpr
      exact ⟨by simpa [i.property] using hAU i.val ha,hn⟩
    have hp (i k : {i : ι // owner i = j}) (hik : i ≠ k) : (E i ∩ E k).card ≤ 1 := by
      apply le_trans (card_le_card ?_) (hpair i.val k.val (by intro he; exact hik (Subtype.ext he)))
      intro a ha
      exact mem_inter.mpr ⟨(mem_sdiff.mp (mem_inter.mp ha).1).1,(mem_sdiff.mp (mem_inter.mp ha).2).1⟩
    have H := PlaneCount.union_lower E (M-D) hEc hp
    have H' : (univ.biUnion E).card ≤ (Region j).card := by
      apply card_le_card
      intro a ha
      obtain ⟨i,hi,ha⟩ := mem_biUnion.mp ha
      exact hE i ha
    have hnum : M ≤ 2*(M-D-u j) := by
      have h1 := hu j
      change 4*D ≤ M at hDM
      omega
    change u j*(M-D-u j) ≤ (univ.biUnion E).card at H
    nlinarith [Nat.mul_le_mul_left (u j) hnum]
  have hregions : (↑(univ : Finset κ) : Set κ).PairwiseDisjoint Region :=
    PlaneCount.exclusive_disjoint P
  have hregionU : univ.biUnion Region ⊆ U := by
    intro a ha
    obtain ⟨j,hj,ha⟩ := mem_biUnion.mp ha
    exact hPU j (mem_sdiff.mp ha).1
  have hsumu : ∑ j, u j = Fintype.card ι := by
    simp only [u,Fintype.card_subtype]
    exact (card_eq_sum_card_fiberwise (s := (univ : Finset ι)) (t := univ)
      (by intro _ _; exact mem_univ _)).symm
  calc
    _ = ∑ j, u j*M := by rw [← sum_mul,hsumu]
    _ ≤ ∑ j, 2*(Region j).card := sum_le_sum (fun j _ => hlocal j)
    _ = 2*(univ.biUnion Region).card := by rw [card_biUnion hregions,mul_sum]
    _ ≤ 2*U.card := Nat.mul_le_mul_left _ (card_le_card hregionU)

end
end SharpLogRamsey.SinglePlaneCount

end

namespace SharpLogRamsey.SurfaceRichLines
open MvPolynomial Finset AffineIncidence
open scoped BigOperators Classical
variable {K : Type*} [Field K] [Infinite K]
noncomputable section
omit [Infinite K] in

lemma plane_crossing (S : Finset (Fin 3 → K)) (x v : Fin 3 → K) (hv : v ≠ 0)
    (L : MvPolynomial (Fin 3) K) (hL : L.totalDegree ≤ 1)
    (hn : LineFlatness.restrictLine x v L ≠ 0) :
    (S.filter (fun y => y ∈ carrier x v ∧ eval y L = 0)).card ≤ 1 := by
  classical
  let A := S.filter (fun y => y ∈ carrier x v ∧ eval y L = 0)
  let f : K → Fin 3 → K := fun t => x+t • v
  let T := A.preimage f (parametrization_injective _ _ hv).injOn
  have hc : T.card = A.card := by
    rw [card_preimage]
    congr 1
    apply filter_eq_self.mpr
    intro y hy
    exact (mem_filter.mp hy).2.1
  have H : T.card ≤ (LineFlatness.restrictLine x v L).natDegree := by
    apply Polynomial.card_le_degree_of_subset_roots
    intro t ht
    apply (Polynomial.mem_roots hn).mpr
    change Polynomial.eval t (LineFlatness.restrictLine x v L) = 0
    rw [RichLinePolynomial.restriction_eval]
    have H := (mem_filter.mp (mem_preimage.mp ht)).2.2
    have he : f t = (fun j => x j+v j*t) := by ext j; simp [f,mul_comm]
    simpa only [he] using H
  rw [hc] at H
  exact H.trans ((RichLinePolynomial.restriction_degree x v L).trans hL)

variable {ι : Type*} [Fintype ι]

theorem card_le {p : ℕ} [CharP K p] [IsAlgClosed K]
    (F : MvPolynomial (Fin 3) K) (hF : F ≠ 0) (hdeg : F.totalDegree < p)
    (hs : Squarefree F) (h2 : (2 : K) ≠ 0)
    (x v : ι → Fin 3 → K) (hv : ∀ i, v i ≠ 0)
    (hd : Function.Injective (fun i => carrier (x i) (v i)))
    (hzero : ∀ i, LineFlatness.restrictLine (x i) (v i) F = 0)
    (S : Finset (Fin 3 → K)) (M Kp : ℕ)
    (hM : ∀ i, M ≤ (onLine x v S i).card)
    (hcap : ∀ L : MvPolynomial (Fin 3) K, L ∣ F → L.totalDegree = 1 →
      (S.filter (fun y => eval y L = 0)).card ≤ Kp)
    (hMD : 6*F.totalDegree < M) (hKM : 8*Kp ≤ M^2) :
    Fintype.card ι ≤ 2*S.card/M+2*S.card/(M-3*F.totalDegree)+8*F.totalDegree^2 := by
  classical
  obtain ⟨planes,G,hG,hGs,hprod,hplanes,hpair,hdiv,hng,hde⟩ :=
    PlaneDecomposition.exists_decomposition F hF hs
  let κ := Fin planes.length
  let L : κ → MvPolynomial (Fin 3) K := planes.get
  have hLd (j : κ) : (L j).totalDegree = 1 := hplanes _ (List.get_mem planes j)
  have hLdiv (j : κ) : L j ∣ F := hdiv _ (List.get_mem planes j)
  have hLc (j k : κ) (hjk : j ≠ k) : IsRelPrime (L j) (L k) := by
    rcases lt_or_gt_of_ne hjk with H | H
    · exact hpair.rel_get_of_lt H
    · exact (hpair.rel_get_of_lt H).symm
  let On : ι → κ → Prop := fun i j => LineFlatness.restrictLine (x i) (v i) (L j) = 0
  let multiple : Finset ι := univ.filter (fun i => ∃ j k, j ≠ k ∧ On i j ∧ On i k)
  let single : Finset ι := univ.filter (fun i => (∃ j, On i j) ∧ i ∉ multiple)
  let none : Finset ι := univ.filter (fun i => ¬∃ j, On i j)
  have hm : multiple.card ≤ 2*F.totalDegree^2 := by
    let Both (j k : κ) := univ.filter (fun i => On i j ∧ On i k)
    have hB (j k : κ) (hjk : j ≠ k) : (Both j k).card ≤ 2 := by
      have H := CommonLines.card_le (L j) (L k) (hLc j k hjk)
        (fun i : Both j k => x i) (fun i : Both j k => v i) (fun i => hv i)
        (fun i l H => Subtype.ext (hd H))
        (fun i t => NonplaneRichLines.eval_of_restrict_zero _ _ _ (mem_filter.mp i.property).2.1 _ ⟨t,rfl⟩)
        (fun i t => NonplaneRichLines.eval_of_restrict_zero _ _ _ (mem_filter.mp i.property).2.2 _ ⟨t,rfl⟩)
      simpa only [Fintype.card_coe,hLd,mul_one] using H
    have hc : multiple ⊆ univ.biUnion (fun j : κ => (univ.erase j).biUnion (Both j)) := by
      intro i hi
      obtain ⟨j,k,hjk,hj,hk⟩ := (mem_filter.mp hi).2
      exact mem_biUnion.mpr ⟨j,mem_univ j,mem_biUnion.mpr
        ⟨k,mem_erase.mpr ⟨hjk.symm,mem_univ k⟩,mem_filter.mpr ⟨mem_univ i,hj,hk⟩⟩⟩
    calc
      _ ≤ (univ.biUnion (fun j : κ => (univ.erase j).biUnion (Both j))).card := card_le_card hc
      _ ≤ ∑ j : κ, ((univ.erase j).biUnion (Both j)).card := card_biUnion_le
      _ ≤ ∑ j : κ, ∑ k ∈ univ.erase j, 2 := by
        apply sum_le_sum
        intro j hj
        apply le_trans card_biUnion_le
        apply sum_le_sum
        intro k hk
        exact hB j k (mem_erase.mp hk).1.symm
      _ ≤ 2*planes.length^2 := by
        simp only [sum_const, Nat.nsmul_eq_mul, card_erase_of_mem (mem_univ _), card_univ]
        have H : planes.length - 1 ≤ planes.length := Nat.sub_le _ _
        dsimp [κ]
        simp only [Fintype.card_fin]
        nlinarith [Nat.mul_le_mul_left planes.length H]
      _ ≤ 2*F.totalDegree^2 := by nlinarith
  have hsing : single.card ≤ 2*S.card/M := by
    have howner : ∀ i : single, ∃ j, On i.val j := fun i => (mem_filter.mp i.property).2.1
    choose owner ho using howner
    have hchoices : ∀ i : single, ∃ A ⊆ onLine x v S i.val, A.card = M :=
      fun i => exists_subset_card_eq (hM i.val)
    choose A hA hAc using hchoices
    let P : κ → Finset (Fin 3 → K) := fun j => S.filter (fun y => eval y (L j) = 0)
    have hAP (i : single) : A i ⊆ P (owner i) := by
      intro y hy
      have hy' := mem_filter.mp (hA i hy)
      apply mem_filter.mpr
      exact ⟨hy'.1,NonplaneRichLines.eval_of_restrict_zero _ _ _ (ho i) y hy'.2⟩
    have hc (i : single) (j : κ) (hj : j ≠ owner i) : (A i ∩ P j).card ≤ 1 := by
      have hn : ¬On i.val j := by
        intro H
        exact (mem_filter.mp i.property).2.2 (mem_filter.mpr ⟨mem_univ i.val,
          j,owner i,hj,H,ho i⟩)
      apply le_trans (card_le_card ?_) (plane_crossing S (x i) (v i) (hv i) (L j) (hLd j).le hn)
      intro y hy
      have hAi := mem_filter.mp (hA i (mem_inter.mp hy).1)
      exact mem_filter.mpr ⟨hAi.1,hAi.2,(mem_filter.mp (mem_inter.mp hy).2).2⟩
    have hp (i k : single) (hik : i ≠ k) : (A i ∩ A k).card ≤ 1 := by
      exact points_intersection_le (fun i : single => x i) (fun i : single => v i)
        (fun i => hv i) (fun i k H => Subtype.ext (hd H)) A
        (fun i _ hy => (mem_filter.mp (hA i hy)).2) i k hik
    have H := SinglePlaneCount.card_mul_le A P owner S M Kp (by omega) hAc hAP
      (fun j => filter_subset _ _) (fun j => hcap (L j) (hLdiv j) (hLd j)) hc hp hKM
      (by simp only [κ,Fintype.card_fin]; omega)
    apply (Nat.le_div_iff_mul_le (by omega)).mpr
    simpa only [Fintype.card_coe] using H
  have hn : none.card ≤ 2*S.card/(M-3*F.totalDegree)+6*F.totalDegree^2 := by
    have hz (i : none) : LineFlatness.restrictLine (x i) (v i) G = 0 := by
      let φ : MvPolynomial (Fin 3) K →ₐ[K] Polynomial K :=
        aeval (fun j => Polynomial.C (x i j)+Polynomial.C (v i j)*Polynomial.X)
      have H : φ F = 0 := hzero i
      rw [hprod,map_mul] at H
      apply (mul_eq_zero.mp H).resolve_left
      intro hp0
      rw [map_list_prod,List.prod_eq_zero_iff,List.mem_map] at hp0
      obtain ⟨J,hJ,hφJ⟩ := hp0
      obtain ⟨j,rfl⟩ := List.mem_iff_get.mp hJ
      exact (mem_filter.mp i.property).2 ⟨j,hφJ⟩
    have H := NonplaneRichLines.card_le G hG (by omega) hGs h2 hng
      (fun i : none => x i) (fun i : none => v i) (fun i => hv i)
      (fun i k H => Subtype.ext (hd H)) hz S M (fun i => hM i) (by omega)
    have H' : none.card ≤ 2*S.card/(M-3*G.totalDegree)+6*G.totalDegree^2 := by
      simpa only [Fintype.card_coe] using H
    apply H'.trans
    apply Nat.add_le_add
    · exact Nat.div_le_div_left (by omega) (by omega)
    · nlinarith
  have hsplit : Fintype.card ι ≤ single.card+multiple.card+none.card := by
    have H : (univ : Finset ι) ⊆ single ∪ multiple ∪ none := by
      intro i hi
      by_cases he : ∃ j, On i j
      · by_cases hm : i ∈ multiple
        · exact mem_union_left _ (mem_union_right _ hm)
        · exact mem_union_left _ (mem_union_left _ (mem_filter.mpr ⟨hi,he,hm⟩))
      · exact mem_union_right _ (mem_filter.mpr ⟨hi,he⟩)
    have H' := (card_le_card H).trans ((card_union_le _ _).trans (Nat.add_le_add_right (card_union_le _ _) _))
    simpa only [card_univ] using H'
  omega

end
end SharpLogRamsey.SurfaceRichLines

end
end

end OAI
end

section
-- module Solutions.OAIQ060_R5.SharpRamsey_Geometry_Weight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Incidence bounds for rich lines and finite point configurations. -/

section
section
section
section
open scoped BigOperators Classical
open Finset
namespace SharpLogRamsey.Sampling
variable {V : Type*} [Fintype V] [DecidableEq V]
omit [DecidableEq V] in

theorem mem_selected (f : V → Bool) (v : V) : v ∈ selected f ↔ f v = true := by
  simp [selected]
omit [DecidableEq V] in

theorem weight_nonneg {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1) (f : V → Bool) :
    0 ≤ weight p f := by
  apply prod_nonneg
  intro v _
  split <;> linarith

theorem sum_weight (p : ℝ) : ∑ f : V → Bool, weight p f = 1 := by
  simp_rw [weight]
  rw [← Fintype.prod_sum (fun (_v : V) (b : Bool) => if b then p else 1-p)]
  simp

theorem containment_moment (p : ℝ) (A : Finset V) :
    (∑ f : V → Bool, weight p f * (if A ⊆ selected f then 1 else 0)) = p^A.card := by
  have hi (f : V → Bool) :
      (if A ⊆ selected f then (1 : ℝ) else 0) =
        ∏ v : V, if v ∈ A then (if f v then 1 else 0) else 1 := by
    by_cases h : A ⊆ selected f
    · rw [ite_eq_left h]
      symm
      apply prod_eq_one
      intro v _
      by_cases hv : v ∈ A
      · simp [hv, (mem_selected f v).mp (h hv)]
      · simp [hv]
    · rw [ite_eq_right h]
      obtain ⟨v, hv, hfv⟩ := not_subset.mp h
      symm
      apply prod_eq_zero (mem_univ v)
      simp only [mem_selected, Bool.not_eq_true] at hfv
      simp [hv, hfv]
  simp_rw [hi, weight, ← prod_mul_distrib]
  rw [← Fintype.prod_sum (fun (v : V) (b : Bool) =>
    (if b then p else 1-p) * (if v ∈ A then (if b then (1:ℝ) else 0) else 1))]
  calc
    _ = ∏ v : V, if v ∈ A then p else 1 := by
      apply prod_congr rfl
      intro v _
      by_cases hv : v ∈ A <;> simp [hv]
    _ = p^A.card := by simp

theorem size_moment (p : ℝ) :
    (∑ f : V → Bool, weight p f * (selected f).card) = p * Fintype.card V := by
  have hc (f : V → Bool) : ((selected f).card : ℝ) =
      ∑ v : V, if ({v} : Finset V) ⊆ selected f then 1 else 0 := by
    simp [selected, sum_boole]
  simp_rw [hc, mul_sum]
  rw [sum_comm]
  simp_rw [containment_moment]
  simp [mul_comm]

theorem exists_ge_mean {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (X : (V → Bool) → ℝ) : ∃ f, (∑ g, weight p g * X g) ≤ X f := by
  obtain ⟨f, _, hf⟩ := exists_max_image (univ : Finset (V → Bool)) X univ_nonempty
  refine ⟨f, ?_⟩
  calc
    (∑ g, weight p g * X g) ≤ ∑ g, weight p g * X f := by
      exact sum_le_sum (fun g _ => mul_le_mul_of_nonneg_left (hf g (mem_univ g))
        (weight_nonneg hp hp1 g))
    _ = X f := by rw [← sum_mul, sum_weight, one_mul]

end SharpLogRamsey.Sampling

namespace SharpLogRamsey.RichSampling
open Sampling Finset
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]
noncomputable section

lemma moment (p b : ℝ) (A : Finset V) :
    (∑ f : V → Bool, weight p f * b^(A ∩ selected f).card) =
      (1-p+p*b)^A.card := by
  have hi (f : V → Bool) : b^(A ∩ selected f).card =
      ∏ v : V, if v ∈ A ∧ f v = true then b else 1 := by
    rw [← prod_filter]
    simp only [prod_const]
    congr 2
    ext v
    simp [selected]
  simp_rw [hi,weight,← prod_mul_distrib]
  rw [← Fintype.prod_sum (fun (v : V) (a : Bool) =>
    (if a then p else 1-p)*(if v ∈ A ∧ a = true then b else 1))]
  calc
    _ = ∏ v : V, if v ∈ A then 1-p+p*b else 1 := by
      apply prod_congr rfl
      intro v hv
      by_cases H : v ∈ A <;> simp [H] ; ring
    _ = _ := by simp

lemma exp_neg_half_le : Real.exp (-(1/2:ℝ)) ≤ 2/3 := by
  have h := Real.add_one_le_exp (1/2:ℝ)
  have he : Real.exp (-(1/2:ℝ))*Real.exp (1/2:ℝ) = 1 := by rw [← Real.exp_add]; norm_num
  have hm := mul_le_mul_of_nonneg_left h (Real.exp_pos (-(1/2:ℝ))).le
  nlinarith

lemma lower_tail (p M : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (A : Finset V) (hM : M ≤ A.card) :
    (∑ f : V → Bool, weight p f *
      (if ((A ∩ selected f).card : ℝ) ≤ p*M/2 then 1 else 0)) ≤
      Real.exp (-p*M/12) := by
  have hpoint (f : V → Bool) :
      (if ((A ∩ selected f).card : ℝ) ≤ p*M/2 then (1:ℝ) else 0) ≤
        Real.exp (p*M/4)*Real.exp (-(1/2:ℝ))^(A ∩ selected f).card := by
    rw [← Real.exp_nat_mul,← Real.exp_add]
    split_ifs with H
    · rw [Real.one_le_exp_iff]
      linarith
    · exact (Real.exp_pos _).le
  have hb0 : 0 ≤ 1-p+p*Real.exp (-(1/2:ℝ)) :=
    add_nonneg (by linarith) (mul_nonneg hp (Real.exp_pos _).le)
  have hb : 1-p+p*Real.exp (-(1/2:ℝ)) ≤ Real.exp (-p/3) := by
    have H := mul_le_mul_of_nonneg_left exp_neg_half_le hp
    have E := Real.add_one_le_exp (-p/3)
    linarith
  calc
    _ ≤ ∑ f : V → Bool, weight p f *
        (Real.exp (p*M/4)*Real.exp (-(1/2:ℝ))^(A ∩ selected f).card) :=
      sum_le_sum (fun f hf => mul_le_mul_of_nonneg_left (hpoint f) (weight_nonneg hp hp1 f))
    _ = Real.exp (p*M/4)*(1-p+p*Real.exp (-(1/2:ℝ)))^A.card := by
      rw [← moment p (Real.exp (-(1/2:ℝ))) A,mul_sum]
      apply sum_congr rfl
      intro f hf
      ring
    _ ≤ Real.exp (p*M/4)*(Real.exp (-p/3))^A.card :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hb0 hb _) (Real.exp_pos _).le
    _ = Real.exp (p*M/4+(A.card:ℝ)*(-p/3)) := by rw [Real.exp_add,Real.exp_nat_mul]
    _ ≤ Real.exp (-p*M/12) := by
      apply Real.exp_le_exp.mpr
      nlinarith [mul_le_mul_of_nonneg_left hM hp]

theorem exists_sample [Nonempty V] (p M : ℝ) (hp : 0 < p) (hp1 : p ≤ 1)
    (L : Finset (Finset V)) (hM : ∀ A ∈ L, M ≤ A.card)
    (hprob : (L.card:ℝ)*Real.exp (-p*M/12) < 1/2) :
    ∃ S : Finset V, (S.card:ℝ) ≤ 2*p*Fintype.card V ∧
      ∀ A ∈ L, p*M/2 < ((A ∩ S).card:ℝ) := by
  classical
  let N : ℝ := Fintype.card V
  have hN : 0 < N := by dsimp [N]; exact_mod_cast (Fintype.card_pos (α := V))
  let bad := fun f : V → Bool => ∑ A ∈ L,
    if ((A ∩ selected f).card:ℝ) ≤ p*M/2 then (1:ℝ) else 0
  let X := fun f : V → Bool => ((selected f).card:ℝ)+2*p*N*bad f
  have hb : (∑ f : V → Bool, weight p f*bad f) ≤
      L.card*Real.exp (-p*M/12) := by
    simp only [bad,mul_sum]
    rw [sum_comm]
    calc
      _ ≤ ∑ _A ∈ L, Real.exp (-p*M/12) :=
        sum_le_sum (fun A hA => lower_tail p M hp.le hp1 A (hM A hA))
      _ = _ := by simp
  have hmean : (∑ f, weight p f*X f) < 2*p*N := by
    have he : (∑ f, weight p f*X f) = p*N+2*p*N*(∑ f, weight p f*bad f) := by
      simp only [X,mul_add,sum_add_distrib]
      rw [size_moment,mul_sum]
      congr 1
      apply sum_congr rfl
      intro f hf
      ring
    rw [he]
    have hlt := hb.trans_lt hprob
    have hpos : 0 < p*N := mul_pos hp hN
    nlinarith
  obtain ⟨f,hf⟩ := exists_ge_mean hp.le hp1 (fun f => -X f)
  simp only [mul_neg,Finset.sum_neg_distrib] at hf
  have hX : X f < 2*p*N := by linarith
  have hb0 : 0 ≤ bad f := by apply sum_nonneg; intro A hA; split_ifs <;> norm_num
  refine ⟨selected f,?_,?_⟩
  · have hcoef : 0 ≤ 2*p*N := by positivity
    change ((selected f).card:ℝ) ≤ 2*p*N
    dsimp only [X] at hX
    nlinarith [mul_nonneg hcoef hb0]
  · intro A hA
    by_contra H
    have ha : ((A ∩ selected f).card:ℝ) ≤ p*M/2 := le_of_not_gt H
    have hb1 : 1 ≤ bad f := by
      have H := single_le_sum (s := L) (f := fun B =>
        if ((B ∩ selected f).card:ℝ) ≤ p*M/2 then (1:ℝ) else 0)
        (fun B hB => by split_ifs <;> norm_num) hA
      simpa only [ite_eq_left ha] using H
    have hcoef : 0 ≤ 2*p*N := by positivity
    have hcard : 0 ≤ ((selected f).card:ℝ) := Nat.cast_nonneg _
    dsimp only [X] at hX
    nlinarith [mul_le_mul_of_nonneg_left hb1 hcoef]

end
end SharpLogRamsey.RichSampling

end

section

namespace SharpLogRamsey.Interpolation
open Finset MvPolynomial
open scoped BigOperators
variable {K : Type*} [Field K]
noncomputable section

lemma exponent_injective (n h : ℕ) : Function.Injective (exponent (n := n) (h := h)) := by
  intro d e H
  ext i
  exact congrArg (fun f : Fin n →₀ ℕ => f i) H

lemma exponent_degree_le {n h : ℕ} (d : Box n h) : (exponent d).degree ≤ n*h := by
  change (exponent d).sum (fun _ e => e) ≤ n*h
  rw [Finsupp.sum_fintype]
  · calc
      ∑ i, (exponent d) i ≤ ∑ _i : Fin n, h := by
        apply sum_le_sum
        intro i hi
        exact Nat.le_of_lt_succ (d i).isLt
      _ = n*h := by simp
  · simp

lemma monomials_independent (n h : ℕ) :
    LinearIndependent K (fun d : Box n h => monomial (exponent d) (1:K)) :=
  (basisMonomials (Fin n) K).linearIndependent.comp exponent (exponent_injective n h)

theorem exists_vanishing (n h : ℕ) (S : Finset (Fin n → K))
    (hS : S.card < (h+1)^n) :
    ∃ F : MvPolynomial (Fin n) K, F ≠ 0 ∧ F.totalDegree ≤ n*h ∧
      ∀ x ∈ S, eval x F = 0 := by
  classical
  let v : Box n h → (S → K) := fun d x => eval x.val (monomial (exponent d) (1:K))
  have hn : ¬LinearIndependent K v := by
    intro H
    have H' := H.fintype_card_le_finrank
    have he : Fintype.card (Box n h) = (h+1)^n := by simp [Box]
    have hf : Module.finrank K (S → K) = S.card := by simp
    rw [he,hf] at H'
    omega
  obtain ⟨c,hc,d,hd⟩ := Fintype.not_linearIndependent_iff.mp hn
  refine ⟨∑ d, c d • monomial (exponent d) (1:K),?_,?_,?_⟩
  · intro H
    exact hd ((Fintype.linearIndependent_iff.mp (monomials_independent (K := K) n h)) c H d)
  · apply totalDegree_finsetSum_le
    intro d hd
    apply (totalDegree_smul_le _ _).trans
    exact (totalDegree_monomial_le _ _).trans (exponent_degree_le d)
  · intro x hx
    have H := congrFun hc ⟨x,hx⟩
    simpa [v,Algebra.smul_def] using H

end
end SharpLogRamsey.Interpolation

end

namespace SharpLogRamsey.SamplePolynomial
open Finset MvPolynomial AffineIncidence
open scoped BigOperators
variable {K V ι : Type*} [Field K] [Fintype V] [Nonempty V] [Fintype ι]
noncomputable section

lemma degree_le_of_dvd {F G : MvPolynomial (Fin 3) K} (hF : F ≠ 0) (h : G ∣ F) :
    G.totalDegree ≤ F.totalDegree := by
  obtain ⟨H,rfl⟩ := h
  have hG : G ≠ 0 := left_ne_zero_of_mul hF
  have hH : H ≠ 0 := right_ne_zero_of_mul hF
  rw [totalDegree_mul_of_isDomain hG hH]
  omega

omit [Fintype ι] in

lemma squarefree_reduction (F : MvPolynomial (Fin 3) K) (hF : F ≠ 0)
    (x v : ι → Fin 3 → K) (hzero : ∀ i, LineFlatness.restrictLine (x i) (v i) F = 0) :
    ∃ G : MvPolynomial (Fin 3) K, G ≠ 0 ∧ Squarefree G ∧
      G.totalDegree ≤ F.totalDegree ∧
      ∀ i, LineFlatness.restrictLine (x i) (v i) G = 0 := by
  obtain ⟨G,n,hG,hGF,hFG⟩ := exists_squarefree_dvd_pow_of_ne_zero hF
  refine ⟨G,ne_zero_of_dvd_ne_zero hF hGF,hG,degree_le_of_dvd hF hGF,?_⟩
  intro i
  have H := map_dvd (aeval (fun j => Polynomial.C (x i j)+Polynomial.C (v i j)*Polynomial.X)) hFG
  change LineFlatness.restrictLine (x i) (v i) F ∣
    (aeval (fun j => Polynomial.C (x i j)+Polynomial.C (v i j)*Polynomial.X)) (G^n) at H
  rw [hzero i,map_pow] at H
  exact eq_zero_of_pow_eq_zero (zero_dvd_iff.mp H)

theorem exists_polynomial (points : V → Fin 3 → K) (hinj : Function.Injective points)
    (x v : ι → Fin 3 → K) (hv : ∀ i, v i ≠ 0)
    (A : ι → Finset V) (hA : ∀ i a, a ∈ A i → points a ∈ carrier (x i) (v i))
    (p M : ℝ) (hp : 0 < p) (hp1 : p ≤ 1) (hM : ∀ i, M ≤ (A i).card)
    (hprob : (Fintype.card ι:ℝ)*Real.exp (-p*M/12) < 1/2)
    (h : ℕ) (hsize : 2*p*Fintype.card V < ((h+1)^3:ℕ)) (hdeg : (3*h:ℕ) ≤ p*M/2) :
    ∃ F : MvPolynomial (Fin 3) K, F ≠ 0 ∧ Squarefree F ∧ F.totalDegree ≤ 3*h ∧
      ∀ i, LineFlatness.restrictLine (x i) (v i) F = 0 := by
  classical
  let L := univ.image A
  have hL : (L.card:ℝ)*Real.exp (-p*M/12) < 1/2 := by
    have hc : L.card ≤ Fintype.card ι := (card_image_le).trans_eq (card_univ)
    exact (mul_le_mul_of_nonneg_right (by exact_mod_cast hc) (Real.exp_pos _).le).trans_lt hprob
  obtain ⟨S,hS,hall⟩ := RichSampling.exists_sample p M hp hp1 L
    (by intro B hB; obtain ⟨i,hi,rfl⟩ := mem_image.mp hB; exact hM i) hL
  let T := S.image points
  have hT : T.card < (h+1)^3 := by
    have he : T.card = S.card := card_image_of_injective S hinj
    rw [he]
    exact_mod_cast hS.trans_lt hsize
  obtain ⟨F,hF,hFd,hFT⟩ := Interpolation.exists_vanishing 3 h T hT
  have hzero (i : ι) : LineFlatness.restrictLine (x i) (v i) F = 0 := by
    let B := (A i ∩ S).image points
    let f : K → Fin 3 → K := fun t => x i+t • v i
    let R := B.preimage f (parametrization_injective _ _ (hv i)).injOn
    have hR : R.card = (A i ∩ S).card := by
      rw [card_preimage]
      have he : B.filter (fun y => y ∈ Set.range f) = B := by
        apply filter_eq_self.mpr
        intro y hy
        obtain ⟨a,ha,rfl⟩ := mem_image.mp hy
        exact hA i a (mem_inter.mp ha).1
      rw [he,card_image_of_injective _ hinj]
    have hr : F.totalDegree < R.card := by
      rw [hR]
      have H := (show (3*h:ℕ) ≤ p*M/2 from hdeg).trans_lt (hall (A i) (mem_image.mpr ⟨i,mem_univ i,rfl⟩))
      have H' : 3*h < (A i ∩ S).card := by exact_mod_cast H
      exact hFd.trans_lt H'
    apply RichLinePolynomial.restriction_zero_of_many (x i) (v i) F R hr
    intro t ht
    have H : f t ∈ B := mem_preimage.mp ht
    obtain ⟨a,ha,he⟩ := mem_image.mp H
    have he' : points a = (fun j => x i j+v i j*t) := by
      rw [he]
      ext j
      simp [f,mul_comm]
    rw [← he']
    exact hFT (points a) (mem_image.mpr ⟨a,(mem_inter.mp ha).2,rfl⟩)
  obtain ⟨G,hG,hGs,hGd,hGz⟩ := squarefree_reduction F hF x v hzero
  exact ⟨G,hG,hGs,hGd.trans hFd,hGz⟩

end
end SharpLogRamsey.SamplePolynomial

end

namespace SharpLogRamsey.RichAffineLines
open Finset MvPolynomial AffineIncidence
open scoped BigOperators Classical
variable {K ι : Type*} [Field K] [Infinite K] [IsAlgClosed K] [Fintype ι]
noncomputable section

theorem card_mul_le {q : ℕ} [CharP K q] (h2 : (2:K) ≠ 0)
    (S : Finset (Fin 3 → K)) (hS : S.Nonempty)
    (x v : ι → Fin 3 → K) (hv : ∀ i, v i ≠ 0)
    (hd : Function.Injective (fun i => carrier (x i) (v i)))
    (M Kp h C : ℕ) (p : ℝ) (hp : 0 < p) (hp1 : p ≤ 1)
    (hM : ∀ i, M ≤ (onLine x v S i).card)
    (hcap : ∀ L : MvPolynomial (Fin 3) K, L.totalDegree = 1 →
      (S.filter (fun y => eval y L = 0)).card ≤ Kp)
    (hprob : (Fintype.card ι:ℝ)*Real.exp (-p*M/12) < 1/2)
    (hsize : 2*p*S.card < ((h+1)^3:ℕ)) (hdeg : (3*h:ℕ) ≤ p*M/2)
    (hchar : 3*h < q) (hMD : 18*h < M) (hKM : 8*Kp ≤ M^2)
    (hD : h^2*M ≤ C*S.card) :
    Fintype.card ι*M ≤ (6+72*C)*S.card := by
  classical
  let : Nonempty S := hS.to_subtype
  let A : ι → Finset S := fun i => univ.filter (fun y => y.val ∈ carrier (x i) (v i))
  have hAc (i : ι) : (A i).card = (onLine x v S i).card := by
    apply card_bij (fun y _ => y.val)
    · intro y hy
      exact mem_filter.mpr ⟨y.property,(mem_filter.mp hy).2⟩
    · intro a ha b hb H
      exact Subtype.ext H
    · intro y hy
      exact ⟨⟨y,(mem_filter.mp hy).1⟩,mem_filter.mpr ⟨mem_univ _,(mem_filter.mp hy).2⟩,rfl⟩
  obtain ⟨F,hF,hFs,hFd,hFz⟩ := SamplePolynomial.exists_polynomial
    (fun y : S => y.val) Subtype.val_injective x v hv A
    (fun i y hy => (mem_filter.mp hy).2) p M hp hp1
    (fun i => by rw [Nat.cast_le]; rw [hAc i]; exact hM i) hprob h
    (by simpa only [Fintype.card_coe] using hsize) hdeg
  have H := SurfaceRichLines.card_le F hF (hFd.trans_lt hchar) hFs h2
    x v hv hd hFz S M Kp hM (fun L _ H => hcap L H) (by omega) hKM
  have HM : 0 < M := by omega
  have HM' : 0 < M-3*F.totalDegree := by omega
  have HD' : M ≤ 2*(M-3*F.totalDegree) := by omega
  have H1 : (2*S.card/M)*M ≤ 2*S.card := Nat.div_mul_le_self _ _
  have H2 : (2*S.card/(M-3*F.totalDegree))*M ≤ 4*S.card := by
    calc
      _ ≤ (2*S.card/(M-3*F.totalDegree))*(2*(M-3*F.totalDegree)) := Nat.mul_le_mul_left _ HD'
      _ = 2*((2*S.card/(M-3*F.totalDegree))*(M-3*F.totalDegree)) := by ring
      _ ≤ 2*(2*S.card) := Nat.mul_le_mul_left _ (Nat.div_mul_le_self _ _)
      _ = _ := by ring
  have H3 : 8*F.totalDegree^2*M ≤ 72*C*S.card := by
    calc
      _ ≤ 8*(3*h)^2*M := Nat.mul_le_mul_right M (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hFd _))
      _ = 72*(h^2*M) := by ring
      _ ≤ 72*(C*S.card) := Nat.mul_le_mul_left _ hD
      _ = _ := by ring
  have HX := Nat.mul_le_mul_right M H
  nlinarith

end
end SharpLogRamsey.RichAffineLines
end

end

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_CardMul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open scoped BigOperators
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal
namespace SharpRamseyFive.ProjectiveRichLines
open Module
open scoped LinearAlgebra.Projectivization Classical
open AffineRealization
variable {K L I ι J : Type*} [Field K] [Field L] [Algebra K L]
    [IsAlgClosed L] [Fintype I] [Fintype ι] [Nonempty ι] [Fintype J]

theorem card_mul_le {q : ℕ} [CharP L q] (h2 : (2:L) ≠ 0)
    (hI : Fintype.card I = 4 ∨ Fintype.card I = 5)
    (p : ι → ℙ K (I → K)) (hp : Function.Injective p)
    (W : J → Submodule K (I → K)) (hW : ∀ l, finrank K (W l) = 2)
    (hWinj : Function.Injective W)
    (M Kp h C : ℕ) (f : ℝ) (hf : 0 < f) (hf1 : f ≤ 1) (hM2 : 2 ≤ M)
    (hM : ∀ l, M ≤ (Finset.univ.filter (fun i => (p i).rep ∈ W l)).card)
    (hcap : ∀ U : Submodule K (I → K), finrank K U = 3 →
      (Finset.univ.filter (fun i => (p i).rep ∈ U)).card ≤ Kp)
    (hprob : (Fintype.card J:ℝ)*Real.exp (-f*M/12) < 1/2)
    (hsize : 2*f*Fintype.card ι < ((h+1)^3:ℕ)) (hdeg : (3*h:ℕ) ≤ f*M/2)
    (hchar : 3*h < q) (hMD : 18*h < M) (hKM : 8*Kp ≤ M^2)
    (hD : h^2*M ≤ C*Fintype.card ι) :
    Fintype.card J*M ≤ (6+72*C)*Fintype.card ι := by
  classical
  obtain ⟨a, ha, hr⟩ := exists_projective_realization (L := L) hI p hp
  obtain ⟨i, j, hij, hi, hj⟩ := exists_line_indices p W (fun l => hM2.trans (hM l))
  let S : Finset (Fin 3 → L) := Finset.univ.image a
  have hSc : S.card = Fintype.card ι := by
    rw [Finset.card_image_of_injective _ ha, Finset.card_univ]
  have hSn : S.Nonempty := by
    exact Finset.image_nonempty.mpr Finset.univ_nonempty
  have hv : ∀ l, a (j l)-a (i l) ≠ 0 := by
    intro l he
    exact hij l (ha (sub_eq_zero.mp he).symm)
  have hlines : ∀ l, M ≤ (SharpLogRamsey.AffineIncidence.onLine
      (fun l => a (i l)) (fun l => a (j l)-a (i l)) S l).card := by
    intro l
    have hc := line_count_of_ranks p hp a ha hr (W l) (hW l) (hij l) (hi l) (hj l)
    exact (hM l).trans_eq hc
  have hcap' (P : MvPolynomial (Fin 3) L) (hP : P.totalDegree = 1) :
      (S.filter (fun y => MvPolynomial.eval y P = 0)).card ≤ Kp := by
    exact plane_cap_of_ranks (by omega) p a ha hr Kp hcap P hP
  have hd := distinct_lines_of_ranks p hp a hr W hW hWinj i j hij hi hj
  have H := SharpLogRamsey.RichAffineLines.card_mul_le h2 S hSn
    (fun l => a (i l)) (fun l => a (j l)-a (i l)) hv hd
    M Kp h C f hf hf1 hlines hcap' hprob (by rwa [hSc]) hdeg
    hchar hMD hKM (by rwa [hSc])
  rwa [hSc] at H

theorem quantitative_card_mul_le_oai {q : ℕ} [CharP L q] (h2 : (2:L) ≠ 0)
    (hI : Fintype.card I = 4 ∨ Fintype.card I = 5)
    (p : ι → ℙ K (I → K)) (hp : Function.Injective p)
    (W : J → Submodule K (I → K)) (hW : ∀ l, finrank K (W l) = 2)
    (hWinj : Function.Injective W)
    (M Kp : ℕ) (hM2 : 2 ≤ M) (hMN : M ≤ Fintype.card ι)
    (hM : ∀ l, M ≤ (Finset.univ.filter (fun i => (p i).rep ∈ W l)).card)
    (hcap : ∀ U : Submodule K (I → K), finrank K U = 3 →
      (Finset.univ.filter (fun i => (p i).rep ∈ U)).card ≤ Kp)
    (hlarge : (1024:ℝ)^2*Fintype.card ι ≤ (M:ℝ)^3)
    (hchar : 51*Real.sqrt ((Fintype.card ι:ℝ)/M) < q)
    (hKM : 8*Kp ≤ M^2) :
    Fintype.card J*M ≤ 20814*Fintype.card ι := by
  obtain ⟨f,h,hf,hf1,hsize,hdeg,hcq,hMD,hD,hfe⟩ :=
    RichParameters.exists_sampling_degree (Fintype.card ι) M q (by omega) hMN hlarge hchar
  apply card_mul_le (L := L) h2 hI p hp W hW hWinj M Kp h 289 f hf hf1 hM2 hM hcap
    _ hsize hdeg hcq hMD hKM hD
  have hc := projective_line_pair_packing p hp W hW hWinj M hM
  have hu := RichParameters.pair_exp_bound hM2 hMN hc
  convert hu using 1
  all_goals try with_reducible_and_instances rfl
  congr 2
  rw [neg_mul, hfe]
  ring
end SharpRamseyFive.ProjectiveRichLines

end OAI
end

theorem solution.{u_1, u_2, u_3, u_4, u_5} : type_of% @OAI.SharpRamseyFive.ProjectiveRichLines.quantitative_card_mul_le_oai.{u_1, u_2, u_3, u_4, u_5} := @OAI.SharpRamseyFive.ProjectiveRichLines.quantitative_card_mul_le_oai.{u_1, u_2, u_3, u_4, u_5}
