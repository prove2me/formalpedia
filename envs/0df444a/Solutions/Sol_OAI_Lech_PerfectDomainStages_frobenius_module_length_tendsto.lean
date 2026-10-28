-- Prove2me | solution 1 for OAI.Lech.PerfectDomainStages.frobenius_module_length_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T21:24:16.118743+00:00
-- url     : https://prove2.me/submissions/8fe9cfe6-c893-4709-b554-55f56a32e3ba

import Mathlib
import Definitions.Def_OAIQ032L023
import Theorems.Thm_OAI_Lech_PerfectDomainStages_stage_tensor_length_tendsto

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
-- module Solutions.OAIQ032_LECH.Multiplicity_RootTowerLengthEq
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MvPowerSeries
open scoped Classical
open scoped TensorProduct
open IsLocalRing
open MvPowerSeries IsLocalRing
open scoped ENNReal
open scoped ENNReal TensorProduct Classical DirectSum
open TensorProduct
namespace Lech.RootTower
open scoped ENNReal TensorProduct
variable {A D : Type*} [CommRing A] [CommRing D] [IsLocalRing A] [IsLocalRing D]
  [Algebra A D] [IsLocalHom (algebraMap A D)]

lemma length_eq_of_residue_surjective
    (hres : Function.Surjective (algebraMap (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField D)))
    (M : Type*) [AddCommGroup M] [Module A M] [Module D M] [IsScalarTower A D M] :
    Module.length A M = Module.length D M := by
  rw [IsLocalRing.length_restrictScalars A D M,
    Module.length_eq_of_surjective (R := IsLocalRing.ResidueField D) hres]
  simp

end Lech.RootTower


end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_TraceConductorPerfectOrder
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

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
namespace Lech.TensorInjection

lemma injective_of_basis {R M N ι : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (b : Module.Basis ι R M) (f : M →ₗ[R] N)
    (h : LinearIndependent R (fun i => f (b i))) : Function.Injective f := by
  have he : f = b.constr R (fun i => f (b i)) := by
    apply b.ext
    intro i
    simp
  rw [he]
  exact b.injective_constr_of_linearIndependent h

section Field
variable {K L Q E : Type*} [Field K] [Field L] [Field Q] [CommRing E]
  [Algebra K L] [Algebra K Q] [Algebra K E] [Algebra Q E]
  [IsScalarTower K Q E]

lemma field_product_injective {ι : Type*} (b : Module.Basis ι K L) (f : L →ₐ[K] E)
    (h : LinearIndependent Q (fun i => f (b i))) :
    Function.Injective (Algebra.TensorProduct.productLeftAlgHom (Algebra.ofId Q E) f) := by
  apply injective_of_basis (b.baseChange Q)
    (Algebra.TensorProduct.productLeftAlgHom (Algebra.ofId Q E) f).toLinearMap
  simpa only [AlgHom.toLinearMap_apply, Module.Basis.baseChange_apply,Algebra.TensorProduct.productLeftAlgHom, Algebra.TensorProduct.lift_tmul,
    map_one,one_mul] using h
end Field

section IntegralBase
variable {A K P Q : Type*} [CommRing A] [IsDomain A] [Field K] [Algebra A K]
  [IsFractionRing A K] [CommRing P] [Field Q] [Algebra A P] [Algebra A Q]
  [Algebra K Q] [IsScalarTower A K Q]

omit [IsDomain A] in
 
lemma localized_product_injective (f : P →ₐ[A] Q) (hf : Function.Injective f) :
    Function.Injective (Algebra.TensorProduct.productLeftAlgHom (Algebra.ofId K Q) f) := by
  let : Algebra P (K ⊗[A] P) := Algebra.TensorProduct.rightAlgebra
  let S := Algebra.algebraMapSubmonoid P A⁰
  let F := Algebra.TensorProduct.productLeftAlgHom (Algebra.ofId K Q) f
  apply IsLocalization.injective_of_map_algebraMap_zero (M := S) (K ⊗[A] P) F.toRingHom
  intro x hx
  change F (1 ⊗ₜ[A] x) = 0 at hx
  have hx' : f x = 0 := by
    simpa [F,Algebra.TensorProduct.productLeftAlgHom,Algebra.TensorProduct.lift_tmul] using hx
  have he : x = 0 := (map_eq_zero_iff _ hf).mp hx'
  simp [he]
end IntegralBase

variable {A K D L P Q E : Type*}
  [CommRing A] [IsDomain A] [Field K] [Algebra A K] [IsFractionRing A K]
  [CommRing D] [Algebra A D] [Field L] [Algebra A L] [Algebra K L]
  [IsScalarTower A K L]
  [CommRing P] [Algebra A P] [Module.Flat A P]
  [Field Q] [Algebra A Q] [Algebra K Q] [IsScalarTower A K Q]
  [CommRing E] [Algebra A E] [Algebra K E] [IsScalarTower A K E]
  [Algebra Q E] [IsScalarTower K Q E] [IsScalarTower A Q E]

omit [IsDomain A] in
 

theorem stage_product_injective {ι : Type*} (b : Module.Basis ι K L)
    (fD : D →ₐ[A] L) (hfD : Function.Injective fD)
    (fP : P →ₐ[A] Q) (hfP : Function.Injective fP)
    (fL : L →ₐ[K] E) (hind : LinearIndependent Q (fun i => fL (b i))) :
    Function.Injective (Algebra.TensorProduct.productMap
      ((IsScalarTower.toAlgHom A Q E).comp fP) ((fL.restrictScalars A).comp fD)) := by
  let U := K ⊗[A] P
  let j : U →ₐ[K] Q := Algebra.TensorProduct.productLeftAlgHom (Algebra.ofId K Q) fP
  have hj : Function.Injective j := localized_product_injective fP hfP
  let k : L ⊗[K] U →ₐ[K] L ⊗[K] Q :=
    Algebra.TensorProduct.map (AlgHom.id K L) j
  have hk : Function.Injective k := by
    exact Module.Flat.lTensor_preserves_injective_linearMap (M := L) j.toLinearMap hj
  let e := Algebra.TensorProduct.cancelBaseChange A K K L P
  let v : D ⊗[A] P →ₐ[A] L ⊗[A] P :=
    Algebra.TensorProduct.map fD (AlgHom.id A P)
  have hv : Function.Injective v :=
    Module.Flat.rTensor_preserves_injective_linearMap (M := P) fD.toLinearMap hfD
  let t := Algebra.TensorProduct.productLeftAlgHom (Algebra.ofId Q E) fL
  have ht : Function.Injective t := field_product_injective b fL hind
  let F : P ⊗[A] D →ₐ[A] E := (t.restrictScalars A).comp
    (((Algebra.TensorProduct.comm K L Q).toAlgHom.restrictScalars A).comp
      ((k.restrictScalars A).comp ((e.symm.toAlgHom.restrictScalars A).comp
        (v.comp (Algebra.TensorProduct.comm A P D).toAlgHom))))
  have hF : Function.Injective F := ht.comp
    ((Algebra.TensorProduct.comm K L Q).injective.comp
      (hk.comp (e.symm.injective.comp (hv.comp (Algebra.TensorProduct.comm A P D).injective))))
  have heq : F = Algebra.TensorProduct.productMap
      ((IsScalarTower.toAlgHom A Q E).comp fP) ((fL.restrictScalars A).comp fD) := by
    apply Algebra.TensorProduct.ext'
    intro a d
    simp [F,v,k,j,t,e,Algebra.TensorProduct.productMap,
      Algebra.TensorProduct.productLeftAlgHom, Algebra.TensorProduct.lift_tmul, mul_comm]
    change fL (fD d) * (algebraMap Q E) ((algebraMap K Q) 1 * fP a) = _
    simp
  rwa [heq] at hF
end Lech.TensorInjection


namespace Lech.RootTower
variable (A : Type*) [CommRing A] [IsReduced A] (p : ℕ) [Fact p.Prime] [CharP A p]

lemma rootMap_eq_frobeniusEquiv (n : ℕ) : rootMap A p n =
    (iterateFrobeniusEquiv (PerfectClosure A p) p n).symm.toRingHom.comp
      (PerfectClosure.of A p) := by
  ext a
  apply (iterateFrobeniusEquiv (PerfectClosure A p) p n).injective
  change (rootMap A p n a)^(p^n) = _
  rw [rootMap_pow]
  exact ((iterateFrobeniusEquiv (PerfectClosure A p) p n).apply_symm_apply _).symm

lemma rootMap_flat (hflat : (PerfectClosure.of A p).Flat) (n : ℕ) :
    (rootMap A p n).Flat := by
  rw [rootMap_eq_frobeniusEquiv]
  exact RingHom.Flat.comp hflat (RingHom.Flat.of_bijective
    (iterateFrobeniusEquiv (PerfectClosure A p) p n).symm.bijective)

end Lech.RootTower


namespace Lech.RootTower
variable (K L : Type*) [Field K] [Field L] [Algebra K L]
  (p : ℕ) [Fact p.Prime] [CharP K p] [CharP L p]

 
lemma root_basis_independent [Algebra.IsSeparable K L] {ι : Type*}
    (b : Module.Basis ι K L) (n : ℕ) :
    LinearIndependent (PerfectClosure K p) (fun i => rootMap L p n (b i)) := by
  let : Algebra K (PerfectClosure K p) := (rootMap K p n).toAlgebra
  let : Algebra K (PerfectClosure L p) := ((rootMap L p n).comp (algebraMap K L)).toAlgebra
  let : IsScalarTower K (PerfectClosure K p) (PerfectClosure L p) :=
    IsScalarTower.of_algebraMap_eq' (by
      ext a
      exact (perfectMap_root p (algebraMap K L) n a).symm)
  let f : L →ₐ[K] PerfectClosure L p :=
    { __ := rootMap L p n, commutes' _ := rfl }
  let : IsPurelyInseparable K (PerfectClosure K p) :=
    (isPurelyInseparable_iff_pow_mem K p).mpr (by
      intro x
      obtain ⟨j,a,ha⟩ := IsPRadical.pow_mem (PerfectClosure.of K p) p x
      refine ⟨j, a^(p^n), ?_⟩
      change rootMap K p n (a^(p^n)) = x^(p^j)
      rw [map_pow,rootMap_pow]
      exact ha)
  apply LinearIndependent.map_of_isPurelyInseparable_of_isSeparable (F := K)
  · intro i
    exact (Algebra.IsSeparable.isSeparable K (b i)).map f (rootMap_injective L p n)
  · exact b.linearIndependent.map' f.toLinearMap
      (LinearMap.ker_eq_bot.mpr (rootMap_injective L p n))

end Lech.RootTower


namespace Lech.PerfectStages
open Lech.RootTower Lech.TraceConductor
open scoped TensorProduct
variable (A D K L : Type*) [CommRing A] [IsDomain A] [CommRing D] [IsDomain D]
  [Field K] [Field L] [Algebra A D] [Algebra A K] [IsFractionRing A K]
  [Algebra A L] [Algebra D L] [IsFractionRing D L] [IsScalarTower A D L]
  [Algebra K L] [IsScalarTower A K L] [Algebra.IsSeparable K L]
  (p : ℕ) [Fact p.Prime] [CharP A p] [CharP K p] [CharP L p]

include K in
omit [IsDomain D] in
 
theorem tensorStageMap_injective (hflat : (PerfectClosure.of A p).Flat) (n : ℕ) :
    Function.Injective (tensorStageMap A D L p n) := by
  let P := PerfectClosure A p
  let Q := PerfectClosure K p
  let E := PerfectClosure L p
  let : Algebra A P := (rootMap A p n).toAlgebra
  let : Module.Flat A P := rootMap_flat A p hflat n
  let : Algebra K Q := (rootMap K p n).toAlgebra
  let : Algebra A Q := ((rootMap K p n).comp (algebraMap A K)).toAlgebra
  let : IsScalarTower A K Q := IsScalarTower.of_algebraMap_eq' rfl
  let : Algebra K E := ((rootMap L p n).comp (algebraMap K L)).toAlgebra
  let : Algebra A E := ((rootMap L p n).comp (algebraMap A L)).toAlgebra
  let : IsScalarTower A K E := IsScalarTower.of_algebraMap_eq' (by
    ext a
    exact congrArg (rootMap L p n) (IsScalarTower.algebraMap_apply A K L a))
  let : IsScalarTower K Q E := IsScalarTower.of_algebraMap_eq' (by
    ext a
    exact (perfectMap_root p (algebraMap K L) n a).symm)
  let : IsScalarTower A Q E := IsScalarTower.of_algebraMap_eq' (by
    ext a
    change rootMap L p n (algebraMap A L a) =
      perfectMap p (algebraMap K L) (rootMap K p n (algebraMap A K a))
    rw [perfectMap_root,IsScalarTower.algebraMap_apply A K L])
  let fP : P →ₐ[A] Q :=
    { __ := perfectMap p (algebraMap A K)
      commutes' a := perfectMap_root p (algebraMap A K) n a }
  let fL : L →ₐ[K] E := { __ := rootMap L p n, commutes' _ := rfl }
  have hh := Lech.TensorInjection.stage_product_injective (Module.Free.chooseBasis K L)
    (IsScalarTower.toAlgHom A D L) (IsFractionRing.injective D L)
    fP (perfectMap_injective p _ (IsFractionRing.injective A K)) fL
    (root_basis_independent K L p (Module.Free.chooseBasis K L) n)
  have he : (tensorStageMap A D L p n).toRingHom =
      (Algebra.TensorProduct.productMap ((IsScalarTower.toAlgHom A Q E).comp fP)
        ((fL.restrictScalars A).comp (IsScalarTower.toAlgHom A D L))).toRingHom := by
    apply RingHom.ext
    intro x
    induction x using OAI.tensorInductionOn with
    | tmul a d =>
        change perfectMap p (algebraMap A L) a * rootMap L p n (algebraMap D L d) =
          perfectMap p (algebraMap K L) (perfectMap p (algebraMap A K) a) *
            rootMap L p n (algebraMap D L d)
        congr 1
        have hp := congrArg (fun f : PerfectClosure A p →+* PerfectClosure L p => f a)
          (perfectMap_comp p (algebraMap A K) (algebraMap K L))
        simpa only [RingHom.comp_apply,← IsScalarTower.algebraMap_eq] using hp.symm
    | add x y hx hy => simp only [map_add,hx,hy]
  change Function.Injective (tensorStageMap A D L p n).toRingHom
  rw [he]
  exact hh

end Lech.PerfectStages


namespace Lech.PerfectDomainStages
open Lech.RootTower
open scoped TensorProduct
variable (A D : Type*) [CommRing A] [IsDomain A] [CommRing D] [IsDomain D]
  [Algebra A D] (p : ℕ) [Fact p.Prime] [CharP A p] [CharP D p]

variable (L : Type*) [Field L] [Algebra A L] [Algebra D L] [IsScalarTower A D L]
  [CharP L p]

lemma fieldMap_tensor (n : ℕ) :
    let : Algebra A (PerfectClosure A p) := (rootMap A p n).toAlgebra
    (fieldMap A D p L).comp (tensorMap A D p n) =
      Lech.PerfectStages.tensorStageMap A D L p n := by
  let : Algebra A (PerfectClosure A p) := (rootMap A p n).toAlgebra
  apply AlgHom.ext
  intro x
  induction x using OAI.tensorInductionOn with
  | tmul a d =>
    change perfectMap p (algebraMap D L)
      (perfectMap p (algebraMap A D) a * rootMap D p n d) = _
    rw [map_mul,perfectMap_root]
    change _ = perfectMap p (algebraMap A L) a * rootMap L p n (algebraMap D L d)
    congr 1
    rw [← RingHom.comp_apply,perfectMap_comp,← IsScalarTower.algebraMap_eq]
  | add x y hx hy => simpa only [map_add] using congrArg₂ (·+·) hx hy

variable (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
  [Algebra K L] [IsScalarTower A K L] [IsFractionRing D L]
  [FiniteDimensional K L] [Algebra.IsSeparable K L] [CharP K p]

include L K in
omit [FiniteDimensional K L] in
lemma tensorMap_injective (hflat : (PerfectClosure.of A p).Flat) (n : ℕ) :
    Function.Injective (tensorMap A D p n) := by
  have h := Lech.PerfectStages.tensorStageMap_injective A D K L p hflat n
  have hh := fieldMap_tensor A D p L n
  intro x y hxy
  apply h
  rw [← hh]
  exact congrArg (fieldMap A D p L) hxy

end Lech.PerfectDomainStages
end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_PerfectDomainStagesTensorTo
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
namespace Lech.PerfectDomainStages
open Lech.RootTower
open scoped TensorProduct
variable (A D : Type*) [CommRing A] [IsDomain A] [CommRing D] [IsDomain D]
  [Algebra A D] (p : ℕ) [Fact p.Prime] [CharP A p] [CharP D p]

lemma tensorEquiv_root (n : ℕ) (hi : Function.Injective (tensorMap A D p n)) (d : D) :
    let : Algebra A (PerfectClosure A p) := (rootMap A p n).toAlgebra
    tensorEquiv A D p n hi (1 ⊗ₜ[A] d) = rootToStage A D p n d := by
  let : Algebra A (PerfectClosure A p) := (rootMap A p n).toAlgebra
  apply Subtype.ext
  change tensorMap A D p n (1 ⊗ₜ[A] d) = rootMap D p n d
  rw [tensorMap_apply,map_one,one_mul]

end Lech.PerfectDomainStages


end
end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_FrobeniusModule
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Lech
open scoped TensorProduct

lemma finite_extendScalars {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (M : ModuleCat R) [Module.Finite R M] :
    Module.Finite S ((ModuleCat.extendScalars f).obj M) := by
  let := f.toAlgebra
  change Module.Finite S (S ⊗[R] M)
  infer_instance


instance finite_frobeniusModule (D : Type*) [CommRing D] (p : ℕ) [Fact p.Prime] [CharP D p]
    (n : ℕ) (M : ModuleCat D) [Module.Finite D M] :
    Module.Finite D (FrobeniusModule D p n M) :=
  finite_extendScalars (iterateFrobenius D p n) M
end Lech

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_FrobeniusTensorStage
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.rootStageFunctor_preservesFiniteColimits _root_.OAI.Lech.PerfectDomainStages.rootStageFunctor_preservesZero _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal
open TensorProduct
namespace Lech.PerfectDomainStages
open Lech.RootTower CategoryTheory
universe u
variable (σ : Type) (k D : Type u) [Fintype σ] [Field k] [CommRing D] [IsDomain D] [IsLocalRing D]
  [Algebra (MvPowerSeries σ k) D] [IsLocalHom (algebraMap (MvPowerSeries σ k) D)]
  [Module.Finite (MvPowerSeries σ k) D]
  (p : ℕ) [Fact p.Prime] [CharP k p] [PerfectRing k p] [CharP D p]

attribute [local instance] OAI.Lech.PerfectDomainStages.instIsDomainMvPowerSeries_solutions
lemma normalizedLength_root_stage_tensor
    (hres : Function.Surjective (algebraMap (IsLocalRing.ResidueField (MvPowerSeries σ k))
      (IsLocalRing.ResidueField D))) (N : ModuleCat.{u} D) [Module.Finite D N] (n : ℕ)
    (hi : Function.Injective (tensorMap (MvPowerSeries σ k) D p n)) :
    letI : Algebra D (stage (MvPowerSeries σ k) D p n) :=
      (rootToStage (MvPowerSeries σ k) D p n).toAlgebra
    normalizedLength σ k p ((stage (MvPowerSeries σ k) D p n) ⊗[D] N) =
      ((p : ℝ≥0∞)^(n * Fintype.card σ))⁻¹ * (Module.length D N).toENNReal := by
  let A := MvPowerSeries σ k
  let P := PerfectClosure A p
  let B := stage A D p n
  let : Algebra A P := (rootMap A p n).toAlgebra
  let : Algebra D B := (rootToStage A D p n).toAlgebra
  let : Algebra D (P ⊗[A] D) := Algebra.TensorProduct.rightAlgebra
  let : Module A N := Module.compHom N (algebraMap A D)
  let : IsScalarTower A D N := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let : Module.Finite A N := Module.Finite.trans D N
  let e := tensorEquiv A D p n hi
  let ed : (P ⊗[A] D) ≃ₐ[D] B :=
    { __ := e.toRingEquiv
      commutes' d := tensorEquiv_root A D p n hi d }
  let f : B ⊗[D] N ≃ₗ[P] P ⊗[A] N :=
    (Lech.TensorConductor.congrLeft ed.symm.toLinearEquiv
      (fun r x => e.symm.toLinearEquiv.map_smul r x)).trans (Lech.TensorPushout.equiv A P D N)
  change (regularTower σ k p).length _ = _
  rw [(regularTower σ k p).length_eq_of_equiv f]
  change normalizedLength σ k p (P ⊗[A] N) = _
  rw [normalizedLength_rootBaseChange]
  congr 1
  exact congrArg ENat.toENNReal (length_eq_of_residue_surjective hres N)

lemma normalizedLength_original_stage_tensor
    (hres : Function.Surjective (algebraMap (IsLocalRing.ResidueField (MvPowerSeries σ k))
      (IsLocalRing.ResidueField D))) (M : ModuleCat.{u} D) [Module.Finite D M] (n : ℕ)
    (hi : Function.Injective (tensorMap (MvPowerSeries σ k) D p n)) :
    letI : Algebra D (stage (MvPowerSeries σ k) D p n) :=
      (originalToStage (MvPowerSeries σ k) D p n).toAlgebra
    normalizedLength σ k p ((stage (MvPowerSeries σ k) D p n) ⊗[D] M) =
      ((p : ℝ≥0∞)^(n * Fintype.card σ))⁻¹ *
        (Module.length D (Lech.FrobeniusModule D p n M)).toENNReal := by
  let A := MvPowerSeries σ k
  let P := PerfectClosure A p
  let B := stage A D p n
  let f := originalToStage A D p n
  let g := rootToStage A D p n
  let N := Lech.FrobeniusModule D p n M
  let X := (ModuleCat.extendScalars f).obj M
  let Y := (ModuleCat.extendScalars g).obj N
  let : Algebra D B := f.toAlgebra
  let : Module P X := by
    change Module P (B ⊗[D] M)
    infer_instance
  let : Module P Y := by
    letI : Algebra D B := g.toAlgebra
    change Module P (B ⊗[D] N)
    infer_instance
  let : IsScalarTower P B X := by
    change IsScalarTower P B (B ⊗[D] M)
    infer_instance
  let : IsScalarTower P B Y := by
    let : Algebra D B := g.toAlgebra
    change IsScalarTower P B (B ⊗[D] N)
    infer_instance
  have e : X ≅ Y := by
    dsimp only [X,Y,N,Lech.FrobeniusModule,f,g]
    rw [← rootToStage_original A D p n]
    exact (ModuleCat.extendScalarsComp (iterateFrobenius D p n)
      (rootToStage A D p n)).app M
  have he := (regularTower σ k p).length_eq_of_equiv
    (e.toLinearEquiv.restrictScalars P)
  change (regularTower σ k p).length X = _
  rw [he]
  exact normalizedLength_root_stage_tensor σ k D p hres N n hi
end Lech.PerfectDomainStages

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
namespace Lech.RootTower

lemma flat_colon_membership {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : f.Flat) (a b : R) (c d : S)
    (h : f a * c = f b * d) :
    c ∈ ((Ideal.span ({b} : Set R)).colon {a}).map f := by
  classical
  let : Algebra R S := f.toAlgebra
  let : Module.Flat R S := hf
  have hh : ∑ i : Fin 2, (![a,-b] i) • (![c,d] i) = 0 := by
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      Algebra.smul_def, RingHom.algebraMap_toAlgebra, map_neg, neg_mul]
    simpa only [sub_eq_add_neg] using sub_eq_zero.mpr h
  obtain ⟨k,u,v,hu,hr⟩ := Module.Flat.isTrivialRelation_of_sum_smul_eq_zero (R := R) (M := S) hh
  rw [show c = ∑ j, u 0 j • v j from hu 0]
  apply Ideal.sum_mem
  intro j _
  have hj : u 0 j ∈ (Ideal.span ({b} : Set R)).colon {a} := by
    rw [Submodule.mem_colon_singleton, smul_eq_mul, Ideal.mem_span_singleton]
    have hj := hr j
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, neg_mul] at hj
    refine ⟨u 1 j, ?_⟩
    have he : a * u 0 j = b * u 1 j := sub_eq_zero.mp (by simpa [sub_eq_add_neg] using hj)
    simpa only [mul_comm] using he
  exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem f hj)

lemma Frobenius_map_le_pow {R : Type*} [CommRing R] (p n : ℕ) [Fact p.Prime]
    [CharP R p] (I : Ideal R) :
    I.map (iterateFrobenius R p n) ≤ I ^ (p^n) := by
  rw [Ideal.map_le_iff_le_comap]
  intro x hx
  change iterateFrobenius R p n x ∈ I ^ (p^n)
  rw [iterateFrobenius_def]
  exact Ideal.pow_mem_pow hx _

lemma integral_uniform_denominator {R K : Type*} [CommRing R] [IsDomain R]
    [Field K] [Algebra R K] [IsFractionRing R K] {x : K} (hx : IsIntegral R x) :
    ∃ c : R, c ≠ 0 ∧ ∀ n : ℕ, IsLocalization.IsInteger R (c • x^n) := by
  obtain ⟨s,hs⟩ := hx.fg_adjoin_singleton
  obtain ⟨c,hc⟩ := IsLocalization.exist_integer_multiples_of_finset
    (nonZeroDivisors R) s
  refine ⟨c, nonZeroDivisors.coe_ne_zero c, fun n => ?_⟩
  have hn : x^n ∈ Submodule.span R (s : Set K) := by
    rw [hs]
    exact (Algebra.adjoin R {x}).pow_mem (Algebra.subset_adjoin rfl) n
  have hall : ∀ y ∈ Submodule.span R (s : Set K),
      IsLocalization.IsInteger R ((c : R) • y) := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy => exact hc y hy
    | zero => simpa using (IsLocalization.isInteger_zero (R := R) (S := K))
    | add y z _ _ hy hz => simpa [smul_add] using IsLocalization.isInteger_add hy hz
    | smul a y _ hy =>
        rw [smul_comm]
        exact IsLocalization.isInteger_smul hy
  exact hall _ hn

 

theorem isIntegrallyClosed_of_flat_frobenius (R : Type*) [CommRing R]
    [IsDomain R] [IsNoetherianRing R] (p : ℕ) [Fact p.Prime] [CharP R p]
    (hf : ∀ n, (iterateFrobenius R p n).Flat) : IsIntegrallyClosed R := by
  apply (isIntegrallyClosed_iff (FractionRing R)).mpr
  intro x hx
  obtain ⟨c,hc,hcx⟩ := integral_uniform_denominator hx
  obtain ⟨b,a,ha⟩ := IsLocalization.exists_integer_multiple (nonZeroDivisors R) x
  by_contra hn
  let J := (Ideal.span ({(b : R)} : Set R)).colon {a}
  have hJ : J ≠ ⊤ := by
    intro hJ
    have haJ : a ∈ Ideal.span ({(b : R)} : Set R) := by
      have h1 : (1 : R) ∈ J := hJ ▸ (show (1 : R) ∈ (⊤ : Ideal R) from trivial)
      simpa [J, Submodule.mem_colon_singleton] using h1
    obtain ⟨y,hy⟩ := Ideal.mem_span_singleton.mp haJ
    apply hn
    refine ⟨y, ?_⟩
    apply mul_left_cancel₀ (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors b.property)
    rw [← map_mul, ← hy]
    simpa only [Algebra.smul_def] using ha
  have hcpow (n : ℕ) : c ∈ J ^ (p^n) := by
    obtain ⟨d,hd⟩ := hcx (p^n)
    simp only [Algebra.smul_def] at hd
    have he : (iterateFrobenius R p n) a * c =
        (iterateFrobenius R p n) (b : R) * d := by
      apply IsFractionRing.injective R (FractionRing R)
      simp only [map_mul, iterateFrobenius_def, map_pow]
      change (algebraMap R (FractionRing R) a)^(p^n) * algebraMap R (FractionRing R) c = _
      rw [ha]
      simp only [Algebra.smul_def, mul_pow]
      rw [mul_assoc, mul_comm (x^(p^n)), ← hd]
    exact Frobenius_map_le_pow p n J
      (flat_colon_membership (iterateFrobenius R p n) (hf n) a b c d he)
  apply hc
  apply (Ideal.mem_bot.mp : c ∈ (⊥ : Ideal R) → c = 0)
  rw [← J.iInf_pow_eq_bot_of_isDomain hJ]
  apply Ideal.mem_iInf.mpr
  intro n
  exact Ideal.pow_le_pow_right (by
    exact Nat.le_of_lt (Nat.lt_pow_self (Nat.Prime.one_lt Fact.out))) (hcpow n)

end Lech.RootTower


end
end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_LechLengthLe
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.rootStageFunctor_preservesFiniteColimits _root_.OAI.Lech.PerfectDomainStages.rootStageFunctor_preservesZero _root_.OAI.Lech.extendScalars_additive
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


namespace Lech.RootTower
variable (σ k : Type*) [Fintype σ] [Field k] (p : ℕ) [Fact p.Prime]
  [CharP k p] [PerfectRing k p]

lemma perfectClosure_flat : (PerfectClosure.of (MvPowerSeries σ k) p).Flat := by
  let A := MvPowerSeries σ k
  have hf : (algebraMap (rootRing A p 0) (PerfectClosure A p)).Flat := by
    apply RingHom.flat_algebraMap_iff.mpr
    exact (regularTower σ k p).flat_limit 0
  have h := (RingHom.Flat.of_bijective (rootEquiv A p 0).bijective).comp hf
  have he : (algebraMap (rootRing A p 0) (PerfectClosure A p)).comp
      (rootEquiv A p 0).toRingHom = PerfectClosure.of A p := by
    apply DFunLike.ext
    intro a
    rfl
  change ((algebraMap (rootRing A p 0) (PerfectClosure A p)).comp
    (rootEquiv A p 0).toRingHom).Flat at h
  rwa [he] at h
end Lech.RootTower


end
end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_PerfectTensorLimit
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.rootStageFunctor_preservesFiniteColimits _root_.OAI.Lech.PerfectDomainStages.rootStageFunctor_preservesZero _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal nonZeroDivisors Topology
open Filter
namespace Lech.PerfectDomainStages
open Lech.RootTower
universe u
variable (h : ℕ) (k D : Type u) [Field k] [CommRing D] [IsDomain D] [IsLocalRing D]
  [IsNoetherianRing D]
  [Algebra (MvPowerSeries (Fin h) k) D]
  [IsLocalHom (algebraMap (MvPowerSeries (Fin h) k) D)]
  [Module.Finite (MvPowerSeries (Fin h) k) D]
  (p : ℕ) [Fact p.Prime] [CharP k p] [PerfectRing k p] [CharP D p]
  (K L : Type u) [Field K] [Field L]
  [Algebra (MvPowerSeries (Fin h) k) K] [IsFractionRing (MvPowerSeries (Fin h) k) K]
  [Algebra (MvPowerSeries (Fin h) k) L] [Algebra D L] [IsScalarTower (MvPowerSeries (Fin h) k) D L]
  [Algebra K L] [IsScalarTower (MvPowerSeries (Fin h) k) K L] [IsFractionRing D L]
  [FiniteDimensional K L] [Algebra.IsSeparable K L] [CharP K p] [CharP L p]
local instance perfectTensorLimitPowerSeriesIsDomain : IsDomain (MvPowerSeries (Fin h) k) :=
  NoZeroDivisors.to_isDomain _

include K L in
 

theorem frobenius_module_length_tendsto_oai
    (hf : Function.Injective (algebraMap (MvPowerSeries (Fin h) k) D))
    (hres : Function.Surjective (algebraMap (IsLocalRing.ResidueField (MvPowerSeries (Fin h) k))
      (IsLocalRing.ResidueField D)))
    (M : ModuleCat.{u} D) (hM : IsFiniteLength D M) :
    Tendsto (fun n => ((p : ℝ≥0∞)^(n*h))⁻¹ *
      (Module.length D (Lech.FrobeniusModule D p n M)).toENNReal) atTop
      (𝓝 (normalizedLength (Fin h) k p ((PerfectClosure D p) ⊗[D] M))) := by
  have := (isFiniteLength_iff_isNoetherian_isArtinian.mp hM).1
  let A := MvPowerSeries (Fin h) k
  have hflat := perfectClosure_flat (Fin h) k p
  let : IsIntegrallyClosed A := isIntegrallyClosed_of_flat_frobenius A p
    (fun n => iterateFrobenius_flat (σ := Fin h) (R := k) p n)
  have hi (n : ℕ) := tensorMap_injective A D p L K hflat n
  have ht := stage_tensor_length_tendsto h k D p K L hf hres M hM
  apply ht.congr
  intro n
  simpa only [Fintype.card_fin] using
    normalizedLength_original_stage_tensor (Fin h) k D p hres M n (hi n)

end Lech.PerfectDomainStages

end

end OAI
end

theorem solution.{u} : type_of% @OAI.Lech.PerfectDomainStages.frobenius_module_length_tendsto_oai.{u} := @OAI.Lech.PerfectDomainStages.frobenius_module_length_tendsto_oai.{u}
