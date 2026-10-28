-- Prove2me | solution 1 for OAI.Lech.PerfectDomainStages.normalizedLength_stage_homology
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T21:27:32.857248+00:00
-- url     : https://prove2.me/submissions/142b5e52-2a80-4679-98b4-40a903ed0d14

import Mathlib
import Definitions.Def_DuttaDomain
import Definitions.Def_OAIQ032L018
import Definitions.Def_OAIQ032L023

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

end Lech.PerfectDomainStages

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_FrobeniusHomologyFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex CochainComplex
namespace Lech
universe u
variable {R : Type u} [CommRing R]

lemma finite_shortComplex_homology [IsNoetherianRing R]
    (S : ShortComplex (ModuleCat.{u} R)) [Module.Finite R S.X₂] :
    Module.Finite R S.homology := by
  let : Module.Finite R S.moduleCatLeftHomologyData.H := by
    change Module.Finite R ((LinearMap.ker S.g.hom) ⧸ LinearMap.range S.moduleCatToCycles)
    infer_instance
  exact Module.Finite.equiv S.moduleCatHomologyIso.toLinearEquiv.symm

lemma finite_cochain_homology [IsNoetherianRing R]
    (F : CochainComplex (ModuleCat.{u} R) ℤ) (i : ℤ) [Module.Finite R (F.X i)] :
    Module.Finite R (F.homology i) := by
  let : Module.Finite R (F.sc i).X₂ := by
    change Module.Finite R (F.X i)
    infer_instance
  exact finite_shortComplex_homology (F.sc i)

end Lech

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_FrobeniusComplexStage
attribute [-instance] _root_.OAI.Lech.PerfectDomainStages.rootStageFunctor_preservesFiniteColimits _root_.OAI.Lech.PerfectDomainStages.rootStageFunctor_preservesZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped TensorProduct ENNReal
namespace Lech.PerfectDomainStages
open Lech.RootTower
universe u
variable (A D : Type u) [CommRing A] [IsDomain A] [CommRing D] [IsDomain D]
  [Algebra A D] (p : ℕ) [Fact p.Prime] [CharP A p] [CharP D p]

lemma rootToStage_flat (hflat : (PerfectClosure.of A p).Flat) (n : ℕ)
    (hi : Function.Injective (tensorMap A D p n)) : (rootToStage A D p n).Flat := by
  let P := PerfectClosure A p
  let B := stage A D p n
  let : Algebra A P := (rootMap A p n).toAlgebra
  let : Module.Flat A P := rootMap_flat A p hflat n
  let : Algebra D B := (rootToStage A D p n).toAlgebra
  let : Algebra D (P ⊗[A] D) := Algebra.TensorProduct.rightAlgebra
  let : Module.Flat D (P ⊗[A] D) := Module.Flat.of_linearEquiv
    (Algebra.TensorProduct.commRight A D P).symm.toLinearEquiv
  let e := tensorEquiv A D p n hi
  let ed : (P ⊗[A] D) ≃ₐ[D] B :=
    { __ := e.toRingEquiv
      commutes' d := tensorEquiv_root A D p n hi d }
  exact Module.Flat.of_linearEquiv ed.symm.toLinearEquiv

end Lech.PerfectDomainStages

namespace Lech.PerfectDomainStages
open Lech.RootTower
universe u
variable (h : ℕ) (k D : Type u) [Field k] [CommRing D] [IsDomain D] [IsLocalRing D]
  [IsNoetherianRing D]
  [Algebra (MvPowerSeries (Fin h) k) D]
  [IsLocalHom (algebraMap (MvPowerSeries (Fin h) k) D)]
  [Module.Finite (MvPowerSeries (Fin h) k) D]
  (p : ℕ) [Fact p.Prime] [CharP k p] [PerfectRing k p] [CharP D p]

attribute [local instance] OAI.Lech.PerfectDomainStages.frobeniusComplexStagePowerSeriesIsDomain
lemma normalizedLength_stage_homology_oai
    (hres : Function.Surjective (algebraMap (IsLocalRing.ResidueField (MvPowerSeries (Fin h) k))
      (IsLocalRing.ResidueField D)))
    (F : CochainComplex (ModuleCat.{u} D) ℤ) (hfin : ∀ j,Module.Finite D (F.X j))
    (n : ℕ) (hi : Function.Injective (tensorMap (MvPowerSeries (Fin h) k) D p n)) (i : ℤ) :
    normalizedLength (Fin h) k p ((stageComplex h k D p n F).homology i) =
      ((p : ℝ≥0∞)^(n*h))⁻¹ *
        (Module.length D ((Lech.frobeniusComplex D p n F).homology i)).toENNReal := by
  let A := MvPowerSeries (Fin h) k
  let P := PerfectClosure A p
  let B := stage A D p n
  let f := originalToStage A D p n
  let g := rootToStage A D p n
  let G := Lech.frobeniusComplex D p n F
  let U := ModuleCat.restrictScalars (algebraMap P B)
  have := hfin i
  have : Module.Finite D (G.X i) := Lech.finite_extendScalars (iterateFrobenius D p n) (F.X i)
  have := Lech.finite_cochain_homology G i
  let e := (Lech.restrictionHomologyIso (algebraMap P B)
      (((ModuleCat.extendScalars f).mapHomologicalComplex _).obj F) i) ≪≫
    U.mapIso (homologyMapIso (stageFrobeniusIso A D p n F) i) ≪≫
    U.mapIso (Lech.flatExtensionHomologyIso g
      (rootToStage_flat A D p (perfectClosure_flat (Fin h) k p) n hi) G i)
  have he := (regularTower (Fin h) k p).length_eq_of_equiv e.toLinearEquiv
  apply he.trans
  let : Algebra D B := g.toAlgebra
  let ee : U.obj ((ModuleCat.extendScalars g).obj (G.homology i)) ≃ₗ[P]
      B ⊗[D] (G.homology i) :=
    { __ := AddEquiv.refl _
      map_smul' r x := by
        change B ⊗[D] (G.homology i) at x
        change (algebraMap P B r) • (x : B ⊗[D] (G.homology i)) =
          r • (x : B ⊗[D] (G.homology i))
        exact IsScalarTower.algebraMap_smul B r (x : B ⊗[D] (G.homology i)) }
  apply ((regularTower (Fin h) k p).length_eq_of_equiv ee).trans
  simpa only [Fintype.card_fin,normalizedLength,A,B,G,g] using
    normalizedLength_root_stage_tensor (Fin h) k D p hres (G.homology i) n hi
end Lech.PerfectDomainStages

end

end OAI
end

theorem solution.{u} : type_of% @OAI.Lech.PerfectDomainStages.normalizedLength_stage_homology_oai.{u} := @OAI.Lech.PerfectDomainStages.normalizedLength_stage_homology_oai.{u}
