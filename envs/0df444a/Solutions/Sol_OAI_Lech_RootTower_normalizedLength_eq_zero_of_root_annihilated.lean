-- Prove2me | solution 1 for OAI.Lech.RootTower.normalizedLength_eq_zero_of_root_annihilated
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T21:30:08.877675+00:00
-- url     : https://prove2.me/submissions/2839e9b0-93af-4880-b07f-cb49eeddc542

import Mathlib
import Definitions.Def_DuttaDomain
import Definitions.Def_OAIQ032L023
import Theorems.Thm_OAI_Lech_FrobeniusGrowth_frobenius_error_tendstoENNReal

section
-- module Solutions.OAIQ032_LECH.Multiplicity_RootTowerRootWeight
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.algebra _root_.OAI.Lech.Homogeneous.module _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectDomain _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectNormal _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MvPowerSeries
open scoped Classical
open scoped TensorProduct
open IsLocalRing
open MvPowerSeries IsLocalRing
open scoped ENNReal

open scoped ENNReal TensorProduct Classical DirectSum
namespace Lech.NormalizedLength

namespace Tower
variable {L : Type*} [CommRing L] (T : Tower L)
attribute [instance] localRing noetherian

variable {M N : Type*} [AddCommGroup M] [Module L M]
  [AddCommGroup N] [Module L N]


lemma mem_span_iff_exists_stage {s : Set M} {x : M} :
    x ∈ Submodule.span L s ↔ ∃ n, x ∈ Submodule.span (T.ring n) s := by
  constructor
  · intro hx
    induction hx using Submodule.span_induction with
    | mem y hy => exact ⟨0, Submodule.subset_span hy⟩
    | zero => exact ⟨0, Submodule.zero_mem _⟩
    | add x y hx hy ihx ihy =>
        obtain ⟨n, hn⟩ := ihx
        obtain ⟨m, hm⟩ := ihy
        exact ⟨max n m, add_mem (T.span_mono_stage (le_max_left n m) hn)
          (T.span_mono_stage (le_max_right n m) hm)⟩
    | smul a x hx ih =>
        obtain ⟨n, hn⟩ := ih
        obtain ⟨m, hm⟩ := T.exhaustive a
        exact ⟨max n m, (Submodule.span (T.ring (max n m)) s).smul_mem
          ⟨a, T.mono (le_max_right n m) hm⟩
          (T.span_mono_stage (le_max_left n m) hn)⟩
  · rintro ⟨n, hn⟩
    exact Submodule.span_le_restrictScalars (T.ring n) L s hn

lemma finite_subset_span_stage {s : Finset M} {t : Set M}
    (h : (s : Set M) ⊆ Submodule.span L t) :
    ∃ n, (s : Set M) ⊆ Submodule.span (T.ring n) t := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | @insert x s hx ih =>
      obtain ⟨n, hn⟩ := T.mem_span_iff_exists_stage.mp (h (a := x) (Finset.mem_insert_self x s))
      obtain ⟨m, hm⟩ := ih (fun y hy => h (by simp [hy]))
      refine ⟨max n m, ?_⟩
      intro y hy
      rcases Finset.mem_insert.mp hy with rfl | hy
      · exact T.span_mono_stage (le_max_left n m) hn
      · exact T.span_mono_stage (le_max_right n m) (hm hy)

 
lemma finiteLength_le_of_span_le {s t : Finset M}
    (h : Submodule.span L (s : Set M) ≤ Submodule.span L (t : Set M)) :
    T.finiteLength s ≤ T.finiteLength t := by
  obtain ⟨n, hn⟩ := T.finite_subset_span_stage
    (fun x hx => h (Submodule.subset_span hx))
  apply le_iInf
  intro k
  have hs : Submodule.span (T.ring (max n k)) (s : Set M) ≤
      Submodule.span (T.ring (max n k)) (t : Set M) :=
    Submodule.span_le.mpr fun x hx => T.span_mono_stage (le_max_left n k) (hn hx)
  calc
    T.finiteLength s ≤ T.stage s (max n k) := T.finiteLength_le_stage _ _
    _ ≤ T.stage t (max n k) := mul_le_mul_right
      (ENat.toENNReal_mono (Module.length_le_of_injective (Submodule.inclusion hs)
        (Submodule.inclusion_injective hs))) _
    _ ≤ T.stage t k := T.stage_antitone t (le_max_right n k)

lemma length_eq_finiteLength_of_span_top (s : Finset M)
    (hs : Submodule.span L (s : Set M) = ⊤) : T.length M = T.finiteLength s := by
  apply le_antisymm _ (T.finiteLength_le_length s)
  apply iSup_le
  intro t
  exact T.finiteLength_le_of_span_le (hs.symm ▸ le_top)

end Tower
end Lech.NormalizedLength
end
end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_NormalizedLengthTrivialRelation
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.PerfectDomainStages.rootStageFunctor_preservesFiniteColimits _root_.OAI.Lech.PerfectDomainStages.rootStageFunctor_preservesZero _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectDomain _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectNormal _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MvPowerSeries
open scoped Classical
open scoped TensorProduct
open IsLocalRing
open MvPowerSeries IsLocalRing
open scoped ENNReal
open scoped ENNReal TensorProduct Classical DirectSum
namespace Lech.NormalizedLength
lemma trivialRelation_of_injective_flat_lift {R M N : Type*}
    [CommRing R] [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]
    [Module.Flat R N] (g : N →ₗ[R] M) (hg : Function.Injective g)
    {l : ℕ} {f : Fin l → R} {x : Fin l → M}
    (hx : ∑ i, f i • x i = 0) (y : Fin l → N) (hy : ∀ i, g (y i) = x i) :
    Module.IsTrivialRelation f x := by
  have hz : ∑ i, f i • y i = 0 := by
    apply hg
    simpa only [map_sum, map_smul, hy, map_zero] using hx
  obtain ⟨k, a, z, hz, ha⟩ := Module.Flat.isTrivialRelation_of_sum_smul_eq_zero hz
  refine ⟨k, a, fun j => g (z j), ?_, ha⟩
  intro i
  rw [← hy i, hz i, map_sum]
  simp only [map_smul]
end Lech.NormalizedLength


namespace Lech.NormalizedLength.Tower
variable {L : Type*} [CommRing L] (T : Lech.NormalizedLength.Tower L)

lemma finite_collection_stage {ι : Type*} [Fintype ι] (x : ι → L) (n : ℕ) :
    ∃ m, n ≤ m ∧ ∀ i, x i ∈ T.ring m := by
  classical
  choose k hk using fun i => T.exhaustive (x i)
  refine ⟨max n (Finset.univ.sup k), le_max_left _ _, fun i => ?_⟩
  exact T.mono ((Finset.le_sup (Finset.mem_univ i)).trans (le_max_right _ _)) (hk i)

include T in
lemma nontrivial_limit : Nontrivial L :=
  (Subtype.val_injective : Function.Injective fun x : T.ring 0 => (x : L)).nontrivial

include T in
lemma local_limit : IsLocalRing L := by
  let := T.nontrivial_limit
  apply IsLocalRing.of_isUnit_or_isUnit_one_sub_self
  intro a
  obtain ⟨n, hn⟩ := T.exhaustive a
  exact (IsLocalRing.isUnit_or_isUnit_one_sub_self (⟨a, hn⟩ : T.ring n)).imp
    (T.ring n).subtype.isUnit_map (T.ring n).subtype.isUnit_map

lemma local_to_limit (n : ℕ) : IsLocalHom (algebraMap (T.ring n) L) := by
  constructor
  intro a ha
  obtain ⟨u, hu⟩ := ha
  change (↑u : L) = (a : L) at hu
  obtain ⟨m, hm⟩ := T.exhaustive (↑u⁻¹ : L)
  let k := max n m
  let b : T.ring k := Subring.inclusion (T.mono (le_max_left n m)) a
  have hb : IsUnit b := by
    apply isUnit_iff_exists_inv.mpr
    refine ⟨⟨↑u⁻¹, T.mono (le_max_right n m) hm⟩, ?_⟩
    apply Subtype.ext
    change (a : L) * (↑u⁻¹ : L) = 1
    rw [← hu]
    simp
  let := T.local_inclusion n k (le_max_left n m)
  exact IsLocalHom.map_nonunit a hb

lemma flat_limit (n : ℕ) : Module.Flat (T.ring n) L := by
  apply Module.Flat.of_forall_isTrivialRelation
  intro l f x hx
  obtain ⟨m, hnm, hm⟩ := T.finite_collection_stage x n
  let : Algebra (T.ring n) (T.ring m) := (Subring.inclusion (T.mono hnm)).toAlgebra
  let := T.flat n m hnm
  let φ : T.ring m →ₗ[T.ring n] L :=
    { toFun := fun z => (z : L)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  exact trivialRelation_of_injective_flat_lift φ Subtype.val_injective hx
    (fun i => ⟨x i, hm i⟩) (fun _ => rfl)

lemma faithfullyFlat_limit (n : ℕ) : Module.FaithfullyFlat (T.ring n) L := by
  let := T.local_limit
  let := T.local_to_limit n
  let := T.flat_limit n
  exact Module.FaithfullyFlat.of_flat_of_isLocalHom

end Lech.NormalizedLength.Tower

open TensorProduct
namespace Lech.NormalizedLength
variable {R S L N : Type*} [CommRing R] [CommRing S] [CommRing L]
  [Algebra R S] [Algebra R L] [Algebra S L] [IsScalarTower R S L]
  [AddCommGroup N] [Module R N]

lemma liftBaseChange_mk_injective [Module.FaithfullyFlat S L] :
    Function.Injective ((TensorProduct.mk R L N 1).liftBaseChange S) := by
  have he : (TensorProduct.mk R L N 1).liftBaseChange S =
      (AlgebraTensorModule.cancelBaseChange R S S L N).toLinearMap ∘ₗ
        TensorProduct.mk S L (S ⊗[R] N) 1 := by
    ext x
    simp
  rw [he]
  exact (AlgebraTensorModule.cancelBaseChange R S S L N).injective.comp
    (Module.FaithfullyFlat.tensorProduct_mk_injective (A := S) (B := L) (S ⊗[R] N))

lemma length_span_baseChange [Module.FaithfullyFlat S L] (s : Set N)
    (hs : Submodule.span R s = ⊤) :
    Module.length S (Submodule.span S (TensorProduct.mk R L N 1 '' s)) =
      Module.length S (S ⊗[R] N) := by
  let f := (TensorProduct.mk R L N 1).liftBaseChange S
  have hf : f.range = Submodule.span S (TensorProduct.mk R L N 1 '' s) := by
    rw [LinearMap.range_liftBaseChange, ← Submodule.map_top, ← hs,
      Submodule.map_span, Submodule.span_span_of_tower]
  rw [← hf]
  exact (LinearEquiv.ofInjective f liftBaseChange_mk_injective).length_eq.symm

lemma span_baseChange_eq_top (s : Set N) (hs : Submodule.span R s = ⊤) :
    Submodule.span L (TensorProduct.mk R L N 1 '' s) = ⊤ := by
  rw [← Submodule.baseChange_span, hs, Submodule.baseChange_top]

end Lech.NormalizedLength


namespace Lech.NormalizedLength.Tower
open TensorProduct
variable {L : Type*} [CommRing L] (T : Lech.NormalizedLength.Tower L)

lemma stage_baseChange (n m : ℕ) (hnm : n ≤ m) (N : Type*)
    [AddCommGroup N] [Module (T.ring n) N] (s : Finset N)
    (hs : Submodule.span (T.ring n) (s : Set N) = ⊤) :
    T.stage (s.image (TensorProduct.mk (T.ring n) L N 1)) m =
      T.weight n * (Module.length (T.ring n) N).toENNReal := by
  let : Algebra (T.ring n) (T.ring m) := (Subring.inclusion (T.mono hnm)).toAlgebra
  let : IsScalarTower (T.ring n) (T.ring m) L :=
    IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  let := T.faithfullyFlat_limit m
  let := T.local_inclusion n m hnm
  let := T.flat n m hnm
  rw [stage, Finset.coe_image]
  erw [length_span_baseChange (R := T.ring n) (S := T.ring m) (L := L) _ hs]
  rw [IsLocalRing.length_baseChange (T.ring n) (T.ring m) N, ENat.toENNReal_mul,
    mul_left_comm]
  have hw : T.weight m * (Module.length (T.ring m) ((T.ring m) ⧸
      (IsLocalRing.maximalIdeal (T.ring n)).map (algebraMap (T.ring n) (T.ring m)))).toENNReal =
      T.weight n := T.weight_mul_fiber n m hnm
  rw [hw, mul_comm]

 

lemma length_baseChange (n : ℕ) (N : Type*)
    [AddCommGroup N] [Module (T.ring n) N] [Module.Finite (T.ring n) N] :
    T.length (L ⊗[T.ring n] N) =
      T.weight n * (Module.length (T.ring n) N).toENNReal := by
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := T.ring n) (M := N)
  let t := s.image (TensorProduct.mk (T.ring n) L N 1)
  have ht : Submodule.span L (t : Set (L ⊗[T.ring n] N)) = ⊤ := by
    rw [Finset.coe_image]
    exact span_baseChange_eq_top _ hs
  rw [T.length_eq_finiteLength_of_span_top t ht]
  apply le_antisymm
  · exact (T.finiteLength_le_stage t n).trans_eq (T.stage_baseChange n n le_rfl N s hs)
  · apply le_iInf
    intro m
    calc
      T.weight n * (Module.length (T.ring n) N).toENNReal = T.stage t (max n m) :=
        (T.stage_baseChange n (max n m) (le_max_left _ _) N s hs).symm
      _ ≤ T.stage t m := T.stage_antitone t (le_max_right _ _)

end Lech.NormalizedLength.Tower


namespace Lech.RootTower
open scoped ENNReal TensorProduct
variable (σ k : Type*) [Fintype σ] [Field k] (p : ℕ) [Fact p.Prime]
  [CharP k p] [PerfectRing k p]


lemma normalizedLength_stage (n : ℕ) (M : Type*) [AddCommGroup M]
    [Module (rootRing (MvPowerSeries σ k) p n) M]
    [Module.Finite (rootRing (MvPowerSeries σ k) p n) M] :
    normalizedLength σ k p ((PerfectClosure (MvPowerSeries σ k) p) ⊗[
      rootRing (MvPowerSeries σ k) p n] M) =
    ((p : ℝ≥0∞) ^ (n * Fintype.card σ))⁻¹ *
      (Module.length (rootRing (MvPowerSeries σ k) p n) M).toENNReal := by
  let : Module ((regularTower σ k p).ring n) M := by
    change Module (rootRing (MvPowerSeries σ k) p n) M
    infer_instance
  let : Module.Finite ((regularTower σ k p).ring n) M := by
    change Module.Finite (rootRing (MvPowerSeries σ k) p n) M
    infer_instance
  exact (regularTower σ k p).length_baseChange n M

end Lech.RootTower


namespace Lech.TensorTransport
variable {A B P : Type*} [CommRing A] [CommRing B] [CommRing P]
  (e : A ≃+* B) [Algebra B P]
  (M : Type*) [AddCommGroup M] [Module A M]

lemma twist_tower :
    let : Algebra A B := e.toRingHom.toAlgebra
    let : Module B M := Module.compHom M e.symm.toRingHom
    IsScalarTower A B M := by
  let : Algebra A B := e.toRingHom.toAlgebra
  let : Module B M := Module.compHom M e.symm.toRingHom
  constructor
  intro a b m
  change e.symm (e a * b) • m = a • (e.symm b • m)
  rw [map_mul,e.symm_apply_apply,mul_smul]

lemma twist_length :
    let : Module B M := Module.compHom M e.symm.toRingHom
    Module.length B M = Module.length A M := by
  let : Algebra A B := e.toRingHom.toAlgebra
  let : Module B M := Module.compHom M e.symm.toRingHom
  let : IsScalarTower A B M := twist_tower e M
  exact (Module.length_eq_of_surjective (R := B) (S := A) e.surjective).symm

lemma twist_finite [Module.Finite A M] :
    let : Module B M := Module.compHom M e.symm.toRingHom
    Module.Finite B M := by
  let : Algebra A B := e.toRingHom.toAlgebra
  let : Module B M := Module.compHom M e.symm.toRingHom
  let : IsScalarTower A B M := twist_tower e M
  exact Module.Finite.of_restrictScalars_finite A B M

end Lech.TensorTransport


namespace Lech.RootTower
open scoped ENNReal TensorProduct
variable (σ k : Type*) [Fintype σ] [Field k] (p : ℕ) [Fact p.Prime]
  [CharP k p] [PerfectRing k p]

 

lemma normalizedLength_rootBaseChange (n : ℕ) (M : Type*) [AddCommGroup M]
    [Module (MvPowerSeries σ k) M] [Module.Finite (MvPowerSeries σ k) M] :
    let : Algebra (MvPowerSeries σ k) (PerfectClosure (MvPowerSeries σ k) p) :=
      (rootMap (MvPowerSeries σ k) p n).toAlgebra
    normalizedLength σ k p ((PerfectClosure (MvPowerSeries σ k) p) ⊗[MvPowerSeries σ k] M) =
    ((p : ℝ≥0∞) ^ (n * Fintype.card σ))⁻¹ * (Module.length (MvPowerSeries σ k) M).toENNReal := by
  let A := MvPowerSeries σ k
  let P := PerfectClosure A p
  let B := rootRing A p n
  let e : A ≃+* B := rootEquiv A p n
  let : Algebra A P := (rootMap A p n).toAlgebra
  let : Algebra A B := e.toRingHom.toAlgebra
  let : IsScalarTower A B P := IsScalarTower.of_algebraMap_eq' rfl
  let : Module B M := Module.compHom M e.symm.toRingHom
  let : IsScalarTower A B M := Lech.TensorTransport.twist_tower e M
  let : Module.Finite B M := Lech.TensorTransport.twist_finite e M
  have h := Lech.TensorTransport.reindex (P := P) (M := M) e.surjective
  have he := (regularTower σ k p).length_eq_of_equiv h
  change normalizedLength σ k p (P ⊗[A] M) = _ at he
  change normalizedLength σ k p (P ⊗[A] M) = _
  change normalizedLength σ k p (P ⊗[A] M) = normalizedLength σ k p (P ⊗[B] M) at he
  rw [he,normalizedLength_stage]
  congr 1
  exact congrArg ENat.toENNReal (Lech.TensorTransport.twist_length e M)

end Lech.RootTower
end
end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_SubalgebraStageFromBase
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MvPowerSeries
open scoped Classical
open scoped TensorProduct
open IsLocalRing
open MvPowerSeries IsLocalRing
open scoped ENNReal
open scoped ENNReal TensorProduct Classical DirectSum
open TensorProduct
open scoped TensorProduct nonZeroDivisors

open scoped nonZeroDivisors


namespace Lech.PowerSeries
open MvPowerSeries
variable {σ R : Type*} [Fintype σ] [CommRing R]

lemma pick_zero : pick (0 : σ →₀ ℕ) = none := by simp [pick]
lemma pick_positive {d : σ →₀ ℕ} {i : σ} (hi : pick d = some i) : 0 < d i := by
  classical
  by_cases hd : d = 0
  · subst d; simp [pick] at hi
  · have hc : Classical.choose (exists_positive hd) = i := by
      exact Option.some.inj (by simpa only [pick,dite_eq_right hd] using hi)
    rw [← hc]
    exact Classical.choose_spec (exists_positive hd)

lemma exists_pick {d : σ →₀ ℕ} (hd : d ≠ 0) : ∃ i, pick d = some i := by
  simp [pick,hd]

lemma coeff_divide_X (f : MvPowerSeries σ R) (i : σ) (d : σ →₀ ℕ) :
    coeff d (divide f i * X i) = if pick d = some i then coeff d f else 0 := by
  classical
  rw [X,coeff_mul_monomial]
  by_cases hle : Finsupp.single i 1 ≤ d
  · rw [ite_eq_left hle]
    simp only [mul_one]
    change (if pick (d - Finsupp.single i 1 + Finsupp.single i 1) = some i then
      coeff (d - Finsupp.single i 1 + Finsupp.single i 1) f else 0) = _
    rw [tsub_add_cancel_of_le hle]
  · rw [ite_eq_right hle]
    have hp : pick d ≠ some i := by
      intro hc
      apply hle
      intro j
      by_cases hji : j = i
      · subst j; simpa using (Nat.succ_le_iff.mpr (pick_positive hc))
      · simp [hji]
    simp [hp]

 

lemma sum_divide_X (f : MvPowerSeries σ R) :
    ∑ i, divide f i * X i = f - C (constantCoeff f) := by
  classical
  ext d
  simp only [map_sum,coeff_divide_X,map_sub]
  by_cases hd : d = 0
  · subst d
    simp [pick_zero]
  · obtain ⟨i,hi⟩ := exists_pick hd
    rw [Finset.sum_eq_single i]
    · simp [hi,coeff_C,hd]
    · intro j _ hji
      simp [hi,Ne.symm hji]
    · simp

lemma variables_eq_ker_constantCoeff :
    Ideal.span (Set.range (X : σ → MvPowerSeries σ R)) = RingHom.ker constantCoeff := by
  apply le_antisymm
  · rw [Ideal.span_le]
    rintro _ ⟨i,rfl⟩
    simp
  · intro f hf
    have hc : constantCoeff f = 0 := hf
    have h := sum_divide_X f
    rw [hc,map_zero,sub_zero] at h
    rw [← h]
    exact Ideal.sum_mem _ (fun i _ => Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_range_self i)))

variable {k : Type*} [Field k]
lemma maximalIdeal_eq_variables :
    IsLocalRing.maximalIdeal (MvPowerSeries σ k) =
      Ideal.span (Set.range (X : σ → MvPowerSeries σ k)) := by
  rw [variables_eq_ker_constantCoeff]
  ext f
  simp only [IsLocalRing.mem_maximalIdeal,RingHom.mem_ker,mem_nonunits_iff,isUnit_iff_constantCoeff,
    isUnit_iff_ne_zero,not_not]

end Lech.PowerSeries


namespace Lech.PowerSeries
open MvPowerSeries
variable (σ k : Type*) [Fintype σ] [Field k]

lemma dimension_le_variables : ringKrullDim (MvPowerSeries σ k) ≤ Fintype.card σ := by
  refine (ringKrullDim_le_spanFinrank_maximalIdeal _).trans ?_
  rw [maximalIdeal_eq_variables]
  have h := Submodule.spanFinrank_span_le_ncard_of_finite
    (R := MvPowerSeries σ k) (Set.finite_range (X : σ → MvPowerSeries σ k))
  have hcard : (Set.range (X : σ → MvPowerSeries σ k)).ncard ≤ Fintype.card σ := by
    rw [← Set.image_univ]
    exact (Set.ncard_image_le (Set.finite_univ)).trans (by simp)
  exact_mod_cast h.trans hcard

end Lech.PowerSeries


namespace Lech.PowerSeries
open MvPowerSeries
open scoped nonZeroDivisors
variable (k : Type*) [Field k]

lemma fin_le_dimension (h : ℕ) : (h : WithBot ℕ∞) ≤ ringKrullDim (MvPowerSeries (Fin h) k) := by
  induction h with
  | zero => exact Order.krullDim_nonneg
  | succ h ih =>
    let e : Fin h ↪ Fin (h+1) := Fin.succEmb h
    let f := (killCompl (R := k) e).toRingHom
    have hf : Function.Surjective f := fun x => ⟨rename e x,killCompl_rename_app x⟩
    have hx : (X 0 : MvPowerSeries (Fin (h+1)) k) ∈ (MvPowerSeries (Fin (h+1)) k)⁰ :=
      mem_nonZeroDivisors_iff_ne_zero.mpr (by
        intro hz
        have hc := congrArg (coeff (Finsupp.single 0 1)) hz
        simp at hc)
    have hz : f (X 0) = 0 := by
      apply killCompl_X_eq_zero
      rintro ⟨i,hi⟩
      exact Fin.succ_ne_zero i hi
    have hb := ringKrullDim_succ_le_of_surjective f hf hx hz
    calc
      (↑(h+1) : WithBot ℕ∞) = (h : WithBot ℕ∞) + 1 := by simp
      _ ≤ ringKrullDim (MvPowerSeries (Fin h) k) + 1 := add_le_add ih le_rfl
      _ ≤ _ := hb

lemma fin_dimension (h : ℕ) : ringKrullDim (MvPowerSeries (Fin h) k) = h := by
  apply le_antisymm _ (fin_le_dimension k h)
  simpa using dimension_le_variables (Fin h) k

end Lech.PowerSeries


namespace Lech



theorem dimension_cast (A : Type*) [CommRing A] [IsNoetherianRing A]
    [IsLocalRing A] : (dimension A : WithBot ℕ∞) = ringKrullDim A := by
  have hb := ringKrullDim_ne_bot (R := A)
  have ht := ringKrullDim_ne_top (R := A)
  unfold dimension
  generalize he : ringKrullDim A = d at *
  cases d with
  | bot => exact (hb rfl).elim
  | coe d =>
    simp only [WithBot.unbotD_coe]
    exact congrArg (fun x : ℕ∞ => (x : WithBot ℕ∞))
      (ENat.natCast_toNat (fun h => ht (by simp [h])))



end Lech
end
end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_RootTowerNormalizedLength
attribute [-instance] _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.rootStageFunctor_preservesFiniteColimits _root_.OAI.Lech.PerfectDomainStages.rootStageFunctor_preservesZero _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MvPowerSeries
open scoped Classical
open scoped TensorProduct
open IsLocalRing
open MvPowerSeries IsLocalRing
open scoped ENNReal
open scoped ENNReal TensorProduct Classical DirectSum
open TensorProduct
open scoped TensorProduct nonZeroDivisors
open scoped nonZeroDivisors
open scoped BigOperators
open scoped nonZeroDivisors TensorProduct


namespace Lech.NormalizedLength.Tower
open Filter
open scoped Topology
variable {L : Type*} [CommRing L] (T : Tower L)
  {M : Type*} [AddCommGroup M] [Module L M]

lemma length_fin (n : ℕ) : T.length (Fin n → M) = n * T.length M := by
  induction n with
  | zero => simp [T.length_zero]
  | succ n ih =>
    rw [T.length_eq_of_equiv (Fin.consLinearEquiv L (fun _ : Fin (n+1) => M)).symm,
      T.length_prod, ih, Nat.cast_add, Nat.cast_one, add_mul, one_mul, add_comm]

 
lemma exists_length_le_mul_quotient [Module.Finite L M] :
    ∃ r : ℕ, ∀ I : Ideal L, (∀ a ∈ I, ∀ x : M, a • x = 0) →
      T.length M ≤ r * T.length (L ⧸ I) := by
  classical
  obtain ⟨r,s,hs⟩ := Module.Finite.exists_fin (R := L) (M := M)
  refine ⟨r,fun I hI => ?_⟩
  let fi (i : Fin r) : (L ⧸ I) →ₗ[L] M :=
    I.liftQ (LinearMap.toSpanSingleton L M (s i)) (by
      intro a ha
      exact hI a ha (s i))
  let f : (Fin r → L ⧸ I) →ₗ[L] M := LinearMap.lsum L (fun _ : Fin r => L ⧸ I) L fi
  have hf : Function.Surjective f := by
    rw [← LinearMap.range_eq_top]
    apply le_antisymm le_top
    rw [← hs]
    apply Submodule.span_le.mpr
    rintro _ ⟨i,rfl⟩
    refine ⟨Pi.single i (Ideal.Quotient.mk I 1),?_⟩
    rw [LinearMap.lsum_piSingle]
    change (1 : L) • s i = s i
    exact one_smul _ _
  exact (T.length_le_of_surjective f hf).trans_eq (T.length_fin r)

 

theorem length_eq_zero_of_small_annihilators (I : ℕ → Ideal L)
    (hI : ∀ n a, a ∈ I n → ∀ x : M, a • x = 0)
    (hlim : Tendsto (fun n => T.length (L ⧸ I n)) atTop (𝓝 0)) :
    T.length M = 0 := by
  apply le_antisymm _ bot_le
  apply iSup_le
  intro s
  let U := Submodule.span L (s : Set M)
  have : Module.Finite L U := Module.Finite.of_fg (Submodule.fg_span s.finite_toSet)
  obtain ⟨r,hr⟩ := T.exists_length_le_mul_quotient (M := U)
  have hU : T.length U ≤ 0 := by
    have hlim' := ENNReal.Tendsto.const_mul (a := (r : ℝ≥0∞)) hlim (Or.inr (by simp))
    simp only [mul_zero] at hlim'
    apply ge_of_tendsto hlim'
    exact Filter.Eventually.of_forall fun n => hr (I n) (fun a ha x =>
      Subtype.ext (by exact hI n a ha x))
  exact (T.finiteLength_le_length_of_subset s U Submodule.subset_span).trans hU
end Lech.NormalizedLength.Tower


namespace Lech.RootTower
open Filter
open scoped ENNReal Topology TensorProduct nonZeroDivisors
variable (h : ℕ) (k : Type*) [Field k] (p : ℕ) [Fact p.Prime]
  [CharP k p] [PerfectRing k p]

lemma normalizedLength_base_root_quotient (n : ℕ) (J : Ideal (MvPowerSeries (Fin h) k)) :
    normalizedLength (Fin h) k p ((PerfectClosure (MvPowerSeries (Fin h) k) p) ⧸
      J.map (rootMap (MvPowerSeries (Fin h) k) p n)) =
    ((p : ℝ≥0∞) ^ (n*h))⁻¹ * (Module.length (MvPowerSeries (Fin h) k)
      ((MvPowerSeries (Fin h) k) ⧸ J)).toENNReal := by
  let A := MvPowerSeries (Fin h) k
  let P := PerfectClosure A p
  let : Algebra A P := (rootMap A p n).toAlgebra
  let e := Algebra.TensorProduct.quotIdealMapEquivTensorQuot P J
  have he := (regularTower (Fin h) k p).length_eq_of_equiv e.toLinearEquiv
  change normalizedLength (Fin h) k p (P ⧸ J.map (rootMap A p n)) =
    normalizedLength (Fin h) k p (P ⊗[A] (A ⧸ J)) at he
  rw [he]
  simpa only [Fintype.card_fin] using normalizedLength_rootBaseChange (Fin h) k p n (A ⧸ J)

omit [PerfectRing k p] in
lemma frobenius_root_ideal (H : Ideal (MvPowerSeries (Fin h) k))
    (g : MvPowerSeries (Fin h) k) (n : ℕ) :
    (H.map (iterateFrobenius (MvPowerSeries (Fin h) k) p n) ⊔ Ideal.span {g}).map
      (rootMap (MvPowerSeries (Fin h) k) p n) =
    H.map (PerfectClosure.of (MvPowerSeries (Fin h) k) p) ⊔
      Ideal.span {rootMap (MvPowerSeries (Fin h) k) p n g} := by
  rw [Ideal.map_sup,Ideal.map_span,Set.image_singleton,Ideal.map_map]
  congr 2
  apply DFunLike.ext
  intro a
  exact rootMap_transition (MvPowerSeries (Fin h) k) p 0 n (Nat.zero_le n) a

 

lemma root_scalar_quotient_tendsto (H : Ideal (MvPowerSeries (Fin h) k))
    (hH : H.radical = IsLocalRing.maximalIdeal (MvPowerSeries (Fin h) k))
    {g : MvPowerSeries (Fin h) k} (hg : g ≠ 0) :
    Tendsto (fun n : ℕ => normalizedLength (Fin h) k p
      ((PerfectClosure (MvPowerSeries (Fin h) k) p) ⧸
        (H.map (PerfectClosure.of (MvPowerSeries (Fin h) k) p) ⊔
          Ideal.span {rootMap (MvPowerSeries (Fin h) k) p n g}))) atTop (𝓝 0) := by
  let : IsDomain (MvPowerSeries (Fin h) k) := NoZeroDivisors.to_isDomain _
  have hdim : Lech.dimension (MvPowerSeries (Fin h) k) = h := by
    have hd := Lech.dimension_cast (MvPowerSeries (Fin h) k)
    rw [Lech.PowerSeries.fin_dimension k h] at hd
    exact_mod_cast hd
  have ht := Lech.FrobeniusGrowth.frobenius_error_tendstoENNReal H hH
    (mem_nonZeroDivisors_iff_ne_zero.mpr hg) p
  rw [hdim] at ht
  apply ht.congr
  intro n
  symm
  rw [← frobenius_root_ideal]
  exact normalizedLength_base_root_quotient h k p n _

 
lemma normalizedLength_eq_zero_of_root_annihilated_oai
    (M : Type*) [AddCommGroup M] [Module (PerfectClosure (MvPowerSeries (Fin h) k) p) M]
    (H : Ideal (MvPowerSeries (Fin h) k))
    (hH : H.radical = IsLocalRing.maximalIdeal (MvPowerSeries (Fin h) k))
    {g : MvPowerSeries (Fin h) k} (hg : g ≠ 0)
    (hHM : ∀ a ∈ H, ∀ x : M, PerfectClosure.of (MvPowerSeries (Fin h) k) p a • x = 0)
    (hgM : ∀ n x, rootMap (MvPowerSeries (Fin h) k) p n g • (x : M) = 0) :
    normalizedLength (Fin h) k p M = 0 := by
  apply (regularTower (Fin h) k p).length_eq_zero_of_small_annihilators
    (fun n => H.map (PerfectClosure.of (MvPowerSeries (Fin h) k) p) ⊔
      Ideal.span {rootMap (MvPowerSeries (Fin h) k) p n g})
  · intro n
    have hh : H.map (PerfectClosure.of (MvPowerSeries (Fin h) k) p) ≤ Module.annihilator _ M := by
      rw [Ideal.map_le_iff_le_comap]
      intro a ha
      exact Module.mem_annihilator.mpr (hHM a ha)
    have hg' : Ideal.span {rootMap (MvPowerSeries (Fin h) k) p n g} ≤ Module.annihilator _ M := by
      rw [Ideal.span_singleton_le_iff_mem]
      exact Module.mem_annihilator.mpr (hgM n)
    intro a ha x
    exact Module.mem_annihilator.mp ((sup_le hh hg') ha) x
  · exact root_scalar_quotient_tendsto h k p H hH hg
end Lech.RootTower


open scoped Classical Pointwise
end
end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.Lech.RootTower.normalizedLength_eq_zero_of_root_annihilated_oai.{u_1, u_2} := @OAI.Lech.RootTower.normalizedLength_eq_zero_of_root_annihilated_oai.{u_1, u_2}
