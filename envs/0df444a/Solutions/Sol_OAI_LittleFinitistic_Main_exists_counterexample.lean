-- Prove2me | solution 1 for OAI.LittleFinitistic.Main.exists_counterexample
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T20:13:45.004485+00:00
-- url     : https://prove2.me/submissions/afeb81df-d9b7-4e96-ae61-fb31d96e277c

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_LittleFinitistic
import Definitions.Def_OAIQ023F038

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bar_DirectSumExactness
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.countSum_projective _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.integerCountSum_isKProjective _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideModule _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped DirectSum
noncomputable section
namespace DerivedBar
universe u
variable (D : Type u) [Ring D]
  (S : ℕ → ChainComplex (ModuleCat.{u} D) ℕ)

theorem directSumComplex_d (i j : ℕ) :
    ((directSumComplex S).d i j).hom = DirectSum.lmap (fun r => ((S r).d i j).hom) := by
  by_cases h : j+1=i
  · subst i
    simp only [directSumComplex, ChainComplex.of_d, ModuleCat.hom_ofHom]
    rfl
  · have hrel : ¬ (ComplexShape.down ℕ).Rel i j := h
    rw [(directSumComplex S).shape i j hrel]
    have hf : (fun r => ((S r).d i j).hom) = (fun r => (0 : (S r).X i →ₗ[D] (S r).X j)) := by
      funext r
      rw [(S r).shape i j hrel, ModuleCat.hom_zero]
    rw [hf]
    apply LinearMap.ext
    intro v
    apply DFinsupp.ext
    intro r
    rfl

/-- The original componentwise direct sum is exact at a degree whenever every
summand is exact there. This includes the degree-zero boundary. -/
theorem directSumComplex_exactAt (n : ℕ) (h : ∀ r, (S r).ExactAt n) :
    (directSumComplex S).ExactAt n := by
  rw [HomologicalComplex.exactAt_iff, ShortComplex.moduleCat_exact_iff_range_eq_ker]
  change LinearMap.range (((directSumComplex S).d ((ComplexShape.down ℕ).prev n) n).hom) =
    LinearMap.ker (((directSumComplex S).d n ((ComplexShape.down ℕ).next n)).hom)
  erw [directSumComplex_d, directSumComplex_d, DirectSum.range_lmap, DirectSum.ker_lmap]
  congr 2
  funext r
  exact ShortComplex.Exact.moduleCat_range_eq_ker (h r)

theorem directSumComplex_homology_zero (n : ℕ) (h : ∀ r, IsZero ((S r).homology n)) :
    IsZero ((directSumComplex S).homology n) := by
  rw [← HomologicalComplex.exactAt_iff_isZero_homology]
  exact directSumComplex_exactAt D S n
    (fun r => (HomologicalComplex.exactAt_iff_isZero_homology _ _).mpr (h r))
end DerivedBar

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bar_CountHomologyDetection
attribute [-instance] _root_.OAI.DerivedBar.IterateSupport.isLE_zero _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleTotal.augmentationComparisonOnChains_isIso _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.SelectionEncoding.instRingDirectedAlgebra _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open CategoryTheory CategoryTheory.Limits HomologicalComplex TrivSqZeroExt
noncomputable section
namespace DerivedBar
universe u v w z

theorem nonzero_of_functor_retract {C : Type u} [Category.{v} C]
    {E : Type w} [Category.{z} E] [HasZeroMorphisms E]
    (F : C ⥤ E) {V W : C} (i : V ⟶ W) (p : W ⟶ V) (hip : i ≫ p = 𝟙 V)
    (h : ¬ IsZero (F.obj V)) : ¬ IsZero (F.obj W) := by
  intro hz
  apply h
  rw [IsZero.iff_id_eq_zero]
  have hm := congrArg F.map hip
  rw [F.map_comp, F.map_id] at hm
  rw [← hm, hz.eq_of_tgt (F.map i) 0, zero_comp]

end DerivedBar
namespace DerivedBar.ParityBridge
universe u
variable (k D X : Type u) [Field k] [Ring D] [Algebra k D]
  [AddCommGroup X] [Module k X] [Module D X] [Module Dᵐᵒᵖ X]
  [SMulCommClass D Dᵐᵒᵖ X] [IsScalarTower k D X] [IsScalarTower k Dᵐᵒᵖ X]
variable (N : ModuleCat D)
local notation "A" => TrivSqZeroExt D X
local notation "S" => SquareZero.twoSidedWeightComplex k D X N (inflated_ideal_zero D X N)
local notation "T" => tensorBarComplex k A D N (fstHom k D X)

attribute [local instance] OAI.DerivedBar.ParityBridge.instModuleCarrier_solutions_16
attribute [local instance] OAI.DerivedBar.ParityBridge.instIsScalarTowerCarrier_solutions_16
attribute [local instance] OAI.DerivedBar.ParityBridge.instModuleTrivSqZeroExtCarrier_solutions_15
attribute [local instance] OAI.DerivedBar.ParityBridge.instIsScalarTowerTrivSqZeroExtCarrier_solutions_15
/-- Uniform vanishing of the original count homologies implies vanishing of
the entire actual balanced tensor bar, including its infinite count family. -/
theorem tensorBar_homology_zero_of_counts (n : ℕ) (h : ∀ r, IsZero ((S r).homology n)) :
    IsZero ((T).homology n) :=
  (directSumComplex_homology_zero D S n h).of_iso
    ((HomologicalComplex.homologyFunctor (ModuleCat D) (.down ℕ) n).mapIso
      (SquareZero.tensorCountSplitting k D X N (inflated_ideal_zero D X N)))

theorem tensorBar_homology_nonzero_of_count (r n : ℕ) (h : ¬ IsZero ((S r).homology n)) :
    ¬ IsZero ((T).homology n) :=
  nonzero_of_functor_retract (HomologicalComplex.homologyFunctor (ModuleCat D) (.down ℕ) n)
    (countTensorBarInclusion k D X N r) (countTensorBarProjection k D X N r)
      (countTensorBar_retract k D X N r) h

attribute [local instance] OAI.DerivedBar.ParityBridge.instHasDerivedCategoryModuleCat_solutions_3
/-- Direct input bridge for uniform bounds on the original count objects in
the integer derived category, yielding actual base-change Tor vanishing. -/
theorem baseChangeTor_zero_of_counts (n : ℕ)
    (h : ∀ r, IsZero ((DerivedCategory.homologyFunctor (ModuleCat D) (-(n:ℤ))).obj
      ((integerQ D).obj (S r)))) :
    IsZero (((Balanced.tensorFunctor (fstHom k D X)).leftDerived n).obj (ModuleCat.of A N)) :=
  (tensorBar_homology_zero_of_counts k D X N n
    (fun r => (h r).of_iso (integerQHomologyIso D (S r) n).symm)).of_iso
      (Balanced.tensorBarHomologyIso (fstHom k D X) N n)

/-- A surviving original count homology is a nonzero actual Tor group. -/
theorem baseChangeTor_nonzero_of_count (r n : ℕ)
    (h : ¬ IsZero ((DerivedCategory.homologyFunctor (ModuleCat D) (-(n:ℤ))).obj
      ((integerQ D).obj (S r)))) :
    ¬ IsZero (((Balanced.tensorFunctor (fstHom k D X)).leftDerived n).obj (ModuleCat.of A N)) := by
  intro hz
  have hc : IsZero ((S r).homology n) → False := by
    intro hc
    exact h (hc.of_iso (integerQHomologyIso D (S r) n))
  apply tensorBar_homology_nonzero_of_count k D X N r n hc
  exact hz.of_iso (Balanced.tensorBarHomologyIso (fstHom k D X) N n).symm
end DerivedBar.ParityBridge

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bar_CountTorBounds
attribute [-instance] _root_.OAI.DerivedBar.IterateSupport.isLE_zero _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleTotal.augmentationComparisonOnChains_isIso _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.SelectionEncoding.instRingDirectedAlgebra _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open CategoryTheory CategoryTheory.Limits TrivSqZeroExt
noncomputable section
namespace DerivedBar.ParityBridge
universe u
variable (k D X : Type u) [Field k] [Ring D] [Algebra k D]
  [AddCommGroup X] [Module k X] [Module D X] [Module Dᵐᵒᵖ X]
  [SMulCommClass D Dᵐᵒᵖ X] [IsScalarTower k D X] [IsScalarTower k Dᵐᵒᵖ X]
variable (N : ModuleCat D)
local notation "A" => TrivSqZeroExt D X
local notation "S" => SquareZero.twoSidedWeightComplex k D X N (inflated_ideal_zero D X N)

attribute [local instance] OAI.DerivedBar.ParityBridge.instModuleCarrier_solutions_17
attribute [local instance] OAI.DerivedBar.ParityBridge.instIsScalarTowerCarrier_solutions_17
attribute [local instance] OAI.DerivedBar.ParityBridge.instModuleTrivSqZeroExtCarrier_solutions_16
attribute [local instance] OAI.DerivedBar.ParityBridge.instIsScalarTowerTrivSqZeroExtCarrier_solutions_16
attribute [local instance] OAI.DerivedBar.ParityBridge.instHasDerivedCategoryModuleCat_solutions_4
/-- A uniform upper bound on the original count homologies is a uniform bound
on actual base-change Tor. This is the consumer for Native's uniform count window. -/
theorem baseChangeTor_bounded_of_counts (B : ℕ)
    (h : ∀ r n, B < n →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat D) (-(n:ℤ))).obj
        ((integerQ D).obj (S r)))) :
    ∀ n, B < n →
      IsZero (((Balanced.tensorFunctor (fstHom k D X)).leftDerived n).obj (ModuleCat.of A N)) :=
  fun n hn => baseChangeTor_zero_of_counts k D X N n (fun r => h r n hn)

end DerivedBar.ParityBridge

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bar_ProjectiveTail
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
attribute [-simp] _root_.OAI.ExternalTensor.Section4.sum_hom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace DerivedBar.ProjectiveTail
universe u v
variable {C : Type u} [Category.{v} C] [Abelian C]
variable (K : ChainComplex C ℕ)

theorem cyclesSequence_exact (i : ℕ) : (cyclesSequence K i).Exact :=
  ShortComplex.exact_of_f_is_kernel _ (cyclesSequenceKernel K i)

theorem cyclesSequence_shortExact (i : ℕ) (h : K.ExactAt i) :
    (cyclesSequence K i).ShortExact := by
  have : Epi (K.toCycles (i+1) i) := by
    have hs : (K.sc' (i+1) i ((ComplexShape.down ℕ).next i)).Exact :=
      (K.exactAt_iff' (i+1) i _ (by simp) rfl).mp h
    have hf : K.toCycles (i+1) i ≫
        (K.cyclesIsoSc' (i+1) i _ (by simp) rfl).hom =
        (K.sc' (i+1) i ((ComplexShape.down ℕ).next i)).toCycles := by
      exact K.toCycles_cyclesIsoSc'_hom _ _ _ _ _
    apply (epi_comp_iff_of_isIso (K.toCycles (i+1) i)
      (K.cyclesIsoSc' (i+1) i _ (by simp) rfl).hom).mp
    rw [hf]
    exact hs.epi_toCycles
  have : Mono (cyclesSequence K i).f := inferInstanceAs (Mono (K.iCycles (i+1)))
  have : Epi (cyclesSequence K i).g := inferInstanceAs (Epi (K.toCycles (i+1) i))
  exact ⟨cyclesSequence_exact K i⟩

/-- In an exact tail of projective terms, projective dimension drops by one
at each successive cycle. This does not identify free terms with finite length. -/
theorem cycles_projective (a g : ℕ)
    (he : ∀ i, a ≤ i → K.ExactAt i)
    (hp : ∀ i, Projective (K.X i))
    (hd : HasProjectiveDimensionLE (K.cycles a) g) :
    Projective (K.cycles (a+g)) := by
  induction g generalizing a with
  | zero => simpa using (projective_iff_hasProjectiveDimensionLE_zero _).mpr hd
  | succ g ih =>
    have hs := cyclesSequence_shortExact K a (he a le_rfl)
    have : Projective (cyclesSequence K a).X₂ := hp (a+1)
    have hnext : HasProjectiveDimensionLE (K.cycles (a+1)) g :=
      (hs.hasProjectiveDimensionLT_X₃_iff g inferInstance).mp hd
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih (a+1) (fun i hi => he i (by omega)) hnext
end DerivedBar.ProjectiveTail

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Bar_SplitProjectiveTail
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
attribute [-simp] _root_.OAI.ExternalTensor.Section4.sum_hom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive CategoryTheory.Category
namespace DerivedBar.ProjectiveTail
universe u v u' v'
variable {C : Type u} [Category.{v} C] [Abelian C]
variable {E : Type u'} [Category.{v'} E] [Abelian E]

/-- A local contracting identity forces exactness, without assumptions on the
first or third term. -/
theorem exact_of_local_contraction (S : ShortComplex C)
    (a : S.X₂ ⟶ S.X₁) (b : S.X₃ ⟶ S.X₂)
    (h : a ≫ S.f + S.g ≫ b = 𝟙 _) : S.Exact := by
  apply S.exact_iff_epi_toCycles.mpr
  have : IsSplitEpi S.toCycles := ⟨⟨{
    section_ := S.iCycles ≫ a
    id := by
      apply (cancel_mono S.iCycles).mp
      rw [Category.assoc, S.toCycles_i]
      have hh := congrArg (fun f => S.iCycles ≫ f) h
      simpa only [comp_add, Category.assoc, S.iCycles_g_assoc, zero_comp,
        add_zero, comp_id, id_comp] using hh }⟩⟩
  infer_instance

variable (K : ChainComplex C ℕ)

/-- Three adjacent split cycle sequences contract the middle degree. -/
theorem contraction_of_splittings (n : ℕ)
    (s0 : (cyclesSequence K n).Splitting)
    (s1 : (cyclesSequence K (n+1)).Splitting)
    (s2 : (cyclesSequence K (n+2)).Splitting) :
    (s1.r ≫ s2.s) ≫ K.d (n+3) (n+2) +
      K.d (n+2) (n+1) ≫ (s0.r ≫ s1.s) = 𝟙 (K.X (n+2)) := by
  have hleft : (s1.r ≫ s2.s) ≫ K.d (n+3) (n+2) =
      s1.r ≫ (cyclesSequence K (n+1)).f := by
    rw [← K.toCycles_i (n+3) (n+2)]
    change (s1.r ≫ s2.s) ≫ (cyclesSequence K (n+2)).g ≫
      (cyclesSequence K (n+1)).f = _
    simp only [Category.assoc, s2.s_g_assoc]
  have hright : K.d (n+2) (n+1) ≫ (s0.r ≫ s1.s) =
      (cyclesSequence K (n+1)).g ≫ s1.s := by
    rw [← K.toCycles_i (n+2) (n+1)]
    change ((cyclesSequence K (n+1)).g ≫ (cyclesSequence K n).f) ≫
      (s0.r ≫ s1.s) = _
    simp only [Category.assoc, s0.f_r_assoc]
  rw [hleft, hright]
  exact s1.id

/-- Every additive functor preserves exactness in such a split tail. -/
theorem map_exact_of_splittings (F : C ⥤ E) [F.Additive] (n : ℕ)
    (s0 : (cyclesSequence K n).Splitting)
    (s1 : (cyclesSequence K (n+1)).Splitting)
    (s2 : (cyclesSequence K (n+2)).Splitting) :
    ((F.mapHomologicalComplex (.down ℕ)).obj K).ExactAt (n+2) := by
  let L := (F.mapHomologicalComplex (.down ℕ)).obj K
  apply (L.exactAt_iff' (n+3) (n+2) (n+1) (by simp) (by simp)).mpr
  apply exact_of_local_contraction _ (F.map (s1.r ≫ s2.s)) (F.map (s0.r ≫ s1.s))
  change F.map (s1.r ≫ s2.s) ≫ F.map (K.d (n+3) (n+2)) +
    F.map (K.d (n+2) (n+1)) ≫ F.map (s0.r ≫ s1.s) = 𝟙 _
  rw [← F.map_comp, ← F.map_comp, ← F.map_add, contraction_of_splittings K n s0 s1 s2,
    F.map_id]

/-- A global dimension bound makes the exact projective tail split, uniformly
for every additive functor. The harmless two-degree allowance avoids boundary
conventions and suffices for finite cohomological amplitude. -/
theorem map_exact_tail (F : C ⥤ E) [F.Additive] (a g : ℕ)
    (he : ∀ i, a ≤ i → K.ExactAt i)
    (hp : ∀ i, Projective (K.X i))
    (hg : ∀ M : C, HasProjectiveDimensionLE M g)
    (n : ℕ) (hn : a+g+2 ≤ n) :
    ((F.mapHomologicalComplex (.down ℕ)).obj K).ExactAt n := by
  have hc (i : ℕ) (hi : a+g ≤ i) : Projective (K.cycles i) := by
    obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hi
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      cycles_projective K (a+t) g (fun j hj => he j (by omega)) hp (hg _)
  let split (i : ℕ) (hi : a+g ≤ i) : (cyclesSequence K i).Splitting := by
    haveI : Projective (cyclesSequence K i).X₃ := hc i hi
    exact (cyclesSequence_shortExact K i (he i (by omega))).splittingOfProjective
  obtain ⟨t,rfl⟩ := Nat.exists_eq_add_of_le hn
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    map_exact_of_splittings K F (a+g+t)
      (split _ (by omega)) (split _ (by omega)) (split _ (by omega))
end DerivedBar.ProjectiveTail

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Basic
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideModule _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory
namespace LittleFinitistic
universe u
variable (A : Type u) [Ring A]

theorem le_littleFinitisticDimension (M : ModuleCat.{u} A) [Module.Finite A M]
    (h : projectiveDimension M < ⊤) :
    projectiveDimension M ≤ littleFinitisticDimension A := by
  unfold littleFinitisticDimension
  exact le_iSup_of_le M (le_iSup_of_le inferInstance (le_iSup_of_le h le_rfl))

/-- Unbounded finite projective dimensions of actual finitely generated modules
force the little finitistic dimension to be infinite. -/
theorem littleFinitisticDimension_eq_top_of_unbounded
    (h : ∀ n : ℕ, ∃ M : ModuleCat.{u} A, Module.Finite A M ∧
      projectiveDimension M < ⊤ ∧ (n : WithBot ℕ∞) ≤ projectiveDimension M) :
    littleFinitisticDimension A = ⊤ := by
  apply ENat.WithBot.eq_top_iff_forall_ge.mpr
  intro n
  obtain ⟨M, hM, hfinite, hn⟩ := h n
  let := hM
  exact hn.trans (le_littleFinitisticDimension A M hfinite)

/-- The manuscript's concrete lower-bound pattern is sufficient; all finite
projective-dimension premises must still be supplied by the constructed modules. -/
theorem littleFinitisticDimension_eq_top_of_two_mul_bounds
    (h : ∀ m : ℕ, 0 < m → ∃ M : ModuleCat.{u} A, Module.Finite A M ∧
      projectiveDimension M < ⊤ ∧ ((2*m-2 : ℕ) : WithBot ℕ∞) ≤ projectiveDimension M) :
    littleFinitisticDimension A = ⊤ := by
  apply littleFinitisticDimension_eq_top_of_unbounded
  intro n
  obtain ⟨M,hM,hfinite,hm⟩ := h (n+1) (by omega)
  refine ⟨M,hM,hfinite,le_trans ?_ hm⟩
  exact_mod_cast (show n ≤ 2*(n+1)-2 by omega)
end LittleFinitistic

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Dimension_PDRadical
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
namespace LittleFinitistic.PDRadical
open Module LinearMap Submodule
universe u v
variable {A : Type u} [Ring A]
variable (P : Type v) [AddCommGroup P] [Module A P]

/-- The noncommutative Nakayama step used in the manuscript. -/
theorem quotient_radical_nontrivial [Module.Finite A P] [Nontrivial P] :
    Nontrivial (P ⧸ (Ring.jacobson A • (⊤ : Submodule A P))) := by
  apply Submodule.Quotient.nontrivial_iff.mpr
  exact ne_of_lt (Submodule.jacobson_smul_lt_top (R := A) (M := P) ⊤)

end LittleFinitistic.PDRadical

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Dimension_PDDimension
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.OrdinarySimulation.TensorResolution.projectiveTerm _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
attribute [-simp] _root_.OAI.ExternalTensor.Section4.sum_hom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
namespace LittleFinitistic.PDMinimal
open CategoryTheory CategoryTheory.Limits
universe u
variable {k A : Type u} [Field k] [Ring A] [Algebra k A] [FiniteDimensional k A]

lemma cover_subsingleton (M : FiniteModule k A) [Subsingleton M] :
    Subsingleton (cover M).source := by
  have hp : (cover M).π = 0 := Subsingleton.elim _ _
  have hsurj := (cover M).minimal 0 (by simp [hp])
  refine ⟨fun x y => ?_⟩
  obtain ⟨a, ha⟩ := hsurj x
  obtain ⟨b, hb⟩ := hsurj y
  exact ha.symm.trans hb

lemma cover_injective (M : FiniteModule k A) [Module.Projective A M] :
    Function.Injective (cover M).π := by
  obtain ⟨g, hg⟩ := Module.projective_lifting_property (cover M).π LinearMap.id
    (cover M).surjective
  have he : (cover M).π.comp (g.comp (cover M).π) = (cover M).π := by
    rw [← LinearMap.comp_assoc, hg, LinearMap.id_comp]
  have hs := (cover M).minimal _ he
  have hgs : Function.Surjective g := by
    intro x
    obtain ⟨y, hy⟩ := hs x
    exact ⟨(cover M).π y, hy⟩
  have hgp : g.comp (cover M).π = LinearMap.id := by
    ext x
    obtain ⟨y, rfl⟩ := hgs x
    exact congrArg g (DFunLike.congr_fun hg y)
  exact LinearMap.injective_of_comp_eq_id _ _ hgp

lemma next_subsingleton_of_projective (M : FiniteModule k A) [Module.Projective A M] :
    Subsingleton (next M) := by
  have he := LinearMap.ker_eq_bot.mpr (cover_injective M)
  change Subsingleton (LinearMap.ker (cover M).π)
  rw [he]
  infer_instance

/-- Vanishing of a term of the constructed resolution gives the standard
categorical projective-dimension bound. -/
theorem pdLT_of_term_zero (M : FiniteModule k A) (n i : ℕ)
    (hz : Subsingleton (term M (i+n))) :
    HasProjectiveDimensionLT (syzygy M i).cat n := by
  induction n generalizing i with
  | zero =>
    have : Subsingleton (term M i) := by simpa using hz
    have : Subsingleton (syzygy M i) :=
      Function.Surjective.subsingleton (cover _).surjective
    exact (hasProjectiveDimensionLT_zero_iff_isZero _).mpr
      (ModuleCat.isZero_iff_subsingleton.mpr (show Subsingleton (syzygy M i) from inferInstance))
  | succ n ih =>
    have hnext : HasProjectiveDimensionLT (syzygy M (i+1)).cat n :=
      ih (i+1) (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hz)
    have hs := LinearMap.shortExact_shortComplexKer (cover (syzygy M i)).surjective
    exact hs.hasProjectiveDimensionLT_X₃ n hnext inferInstance

lemma syzygy_projective (M : FiniteModule k A) (n i : ℕ)
    (h : HasProjectiveDimensionLT (syzygy M i).cat (n+1)) :
    Projective (syzygy M (i+n)).cat := by
  induction n generalizing i with
  | zero =>
    simpa using projective_iff_hasProjectiveDimensionLT_one.mpr h
  | succ n ih =>
    have hs := LinearMap.shortExact_shortComplexKer (cover (syzygy M i)).surjective
    have hn : HasProjectiveDimensionLT (syzygy M (i+1)).cat (n+1) :=
      (hs.hasProjectiveDimensionLT_X₃_iff n inferInstance).mp h
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih (i+1) hn

/-- Finite projective dimension forces the minimal resolution to terminate. -/
theorem term_zero_of_pdLE (M : FiniteModule k A) (n : ℕ)
    (h : HasProjectiveDimensionLE M.cat n) : Subsingleton (term M (n+1)) := by
  have hp := syzygy_projective M n 0 h
  rw [Nat.zero_add] at hp
  have : Module.Projective A (syzygy M n) :=
    (IsProjective.iff_projective _).mpr (by simpa only [Nat.zero_add, FiniteModule.cat] using hp)
  have : Subsingleton (syzygy M (n+1)) := next_subsingleton_of_projective (syzygy M n)
  exact cover_subsingleton _

/-- The actual minimal-resolution term criterion, proved from covers and
short-exact-sequence dimension shifting. -/
theorem pdLE_iff_term_zero (M : FiniteModule k A) (n : ℕ) :
    HasProjectiveDimensionLE M.cat n ↔ Subsingleton (term M (n+1)) :=
  ⟨term_zero_of_pdLE M n, fun h => pdLT_of_term_zero M (n+1) 0 (by simpa using h)⟩
end LittleFinitistic.PDMinimal

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Dimension_PDResidueTensor
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BalancedTensor.tensorFinite _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.finite _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.leftModule _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.scalarTower _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.PDBarQuotient.leftModule _root_.OAI.LittleFinitistic.PDBarQuotient.leftTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.SelectedPDDetection.residueModuleK _root_.OAI.LittleFinitistic.SelectionEncoding.instRingDirectedAlgebra _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
namespace LittleFinitistic.PDTensor
open LinearMap Submodule
universe u
variable {k A : Type u} [Field k] [Ring A] [Algebra k A]
variable (N : Type u) [AddCommGroup N] [Module k N] [Module A N] [IsScalarTower k A N]

/-- Nakayama proves tensor detection for every finitely generated nonzero module. -/
theorem residueTensor_nontrivial [Module.Finite A N] [Nontrivial N] :
    Nontrivial (BalancedTensor.Tensor k A (Residue (A := A)) N) := by
  have := PDRadical.quotient_radical_nontrivial (A := A) N
  exact (residueTensorEquiv (k := k) N).toEquiv.nontrivial
end LittleFinitistic.PDTensor

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Dimension_PDDetection
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.Multibar.patternTower _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.DerivedBar.termTower _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BalancedTensor.scalarLeftTower _root_.OAI.LittleFinitistic.BalancedTensor.tensorFinite _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.finite _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.leftModule _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.scalarTower _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideModule _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideTower _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleCoefficients.towerLeft _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.PDBarQuotient.leftModule _root_.OAI.LittleFinitistic.PDBarQuotient.leftTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.SelectedPDDetection.residueModuleK _root_.OAI.LittleFinitistic.SelectionEncoding.instRingDirectedAlgebra _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
namespace LittleFinitistic.PDTensor
open CategoryTheory CategoryTheory.Limits
universe u
variable {k A : Type u} [Field k] [Ring A] [Algebra k A]

/-- Nakayama detects zero modules using the actual radical-quotient tensor. -/
theorem residueTensor_subsingleton_iff
    (N : Type u) [AddCommGroup N] [Module k N] [Module A N] [IsScalarTower k A N]
    [Module.Finite A N] :
    Subsingleton (BalancedTensor.Tensor k A (Residue (A := A)) N) ↔ Subsingleton N := by
  constructor
  · intro h
    by_contra hn
    have : Nontrivial N := not_subsingleton_iff_nontrivial.mp hn
    have := residueTensor_nontrivial (k := k) (A := A) N
    obtain ⟨x, y, hxy⟩ := exists_pair_ne (BalancedTensor.Tensor k A (Residue (A := A)) N)
    exact hxy (h.elim x y)
  · intro h
    have := h
    infer_instance

variable [FiniteDimensional k A] (M : PDMinimal.FiniteModule k A)

/-- For the semisimple quotient S, the n-th Tor is zero exactly when the n-th
term of the constructed minimal projective resolution is zero. -/
theorem residueTor_zero_iff_term (n : ℕ) :
    IsZero (Tor (k := k) (Residue (A := A)) M.cat n) ↔
      Subsingleton (PDMinimal.term M n) := by
  let e := torIsoTerm (Residue (A := A)) M residue_annihilated n
  rw [e.isZero_iff]
  change IsZero (ModuleCat.of k (BalancedTensor.Tensor k A (Residue (A := A))
    (ScalarModule k A (PDMinimal.term M n).cat))) ↔ _
  rw [ModuleCat.isZero_iff_subsingleton]
  have : Module.Finite A (ScalarModule k A (PDMinimal.term M n).cat) :=
    show Module.Finite A (PDMinimal.term M n) from inferInstance
  exact residueTensor_subsingleton_iff (k := k) (ScalarModule k A (PDMinimal.term M n).cat)

/-- Projective dimension of a finite-dimensional module over an actual
finite-dimensional algebra is detected by its derived tensor with A/rad A.
No detection theorem is assumed: the proof constructs minimal resolutions. -/
theorem pdLE_iff_residueTor_zero (n : ℕ) :
    HasProjectiveDimensionLE M.cat n ↔
      IsZero (Tor (k := k) (Residue (A := A)) M.cat (n+1)) := by
  rw [PDMinimal.pdLE_iff_term_zero, residueTor_zero_iff_term]

/-- The conclusion uses mathlib's actual numerical projective dimension. -/
theorem projectiveDimension_le_of_residueTor_zero (n : ℕ)
    (h : IsZero (Tor (k := k) (Residue (A := A)) M.cat (n+1))) :
    projectiveDimension M.cat ≤ n :=
  (projectiveDimension_le_iff _ _).mpr ((pdLE_iff_residueTor_zero M n).mpr h)
end LittleFinitistic.PDTensor

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Dimension_PDLowerBound
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.leftModule _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.PDBarQuotient.leftModule _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.SelectedPDDetection.residueModuleK _root_.OAI.LittleFinitistic.SelectionEncoding.instRingDirectedAlgebra _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
namespace LittleFinitistic.PDTensor
open CategoryTheory CategoryTheory.Limits
universe u
variable {k A : Type u} [Field k] [Ring A] [Algebra k A] [FiniteDimensional k A]
variable (U : Type u) [AddCommGroup U] [Module k U] [Module Aᵐᵒᵖ U]
variable (M : PDMinimal.FiniteModule k A)

/-- Any right module detects a lower bound through nonzero Tor; it need not
be flat, finite-dimensional, or annihilated by the radical. -/
theorem tor_zero_of_pdLT (n : ℕ) (h : HasProjectiveDimensionLT M.cat n) :
    IsZero (Tor (k := k) U M.cat n) := by
  have ht : Subsingleton (PDMinimal.term M n) := by
    cases n with
    | zero =>
      have hm := (hasProjectiveDimensionLT_zero_iff_isZero _).mp h
      have : Subsingleton M := ModuleCat.subsingleton_of_isZero hm
      exact PDMinimal.cover_subsingleton M
    | succ n => exact PDMinimal.term_zero_of_pdLE M n h
  have hz : IsZero (PDMinimal.term M n).cat := ModuleCat.isZero_iff_subsingleton.mpr ht
  have hm : IsZero ((model U M).X n) := (tensorFunctor k A U).map_isZero hz
  exact (HomologicalComplex.ExactAt.of_isZero hm).isZero_homology.of_iso (torIsoModel U M n)

theorem le_projectiveDimension_of_nonzero_Tor (n : ℕ)
    (h : ¬ IsZero (Tor (k := k) U M.cat n)) : n ≤ projectiveDimension M.cat := by
  by_contra hn
  exact h (tor_zero_of_pdLT U M n (projectiveDimension_lt_iff.mp (lt_of_not_ge hn)))

theorem lower_bound_of_nonzero_Tor (r n : ℕ) (hrn : r ≤ n)
    (h : ¬ IsZero (Tor (k := k) U M.cat n)) : r ≤ projectiveDimension M.cat := by
  exact le_trans (by exact_mod_cast hrn) (le_projectiveDimension_of_nonzero_Tor U M n h)

/-- Bounded radical-quotient Tor gives finite numerical projective dimension. -/
theorem projectiveDimension_lt_top_of_bounded_residueTor
    (h : ∃ b : ℕ, ∀ n, b < n → IsZero (Tor (k := k) (Residue (A := A)) M.cat n)) :
    projectiveDimension M.cat < ⊤ := by
  obtain ⟨b, hb⟩ := h
  exact lt_of_le_of_lt
    (projectiveDimension_le_of_residueTor_zero M b (hb (b+1) (by omega))) (WithBot.coe_lt_coe.mpr (ENat.natCast_lt_top b))
end LittleFinitistic.PDTensor

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Dimension_PDSquareZero
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
attribute [-simp] _root_.OAI.ExternalTensor.Section4.sum_hom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
namespace LittleFinitistic.PDSquareZero
open Submodule
universe u
variable {A D : Type u} [Ring A] [Ring D]

variable {k : Type u} [Field k] [Algebra k D]
variable (X : Type u) [AddCommGroup X] [Module D X] [Module Dᵐᵒᵖ X]
  [SMulCommClass D Dᵐᵒᵖ X] [Module k X]
  [IsScalarTower k D X] [IsScalarTower k Dᵐᵒᵖ X]

/-- The manuscript's actual split square-zero projection has square-zero kernel. -/
theorem kernel_square_zero (a b : TrivSqZeroExt D X)
    (ha : a ∈ RingHom.ker (TrivSqZeroExt.fstHom k D X).toRingHom)
    (hb : b ∈ RingHom.ker (TrivSqZeroExt.fstHom k D X).toRingHom) : a*b=0 := by
  have ha0 : a.fst=0 := ha
  have hb0 : b.fst=0 := hb
  apply TrivSqZeroExt.ext <;> simp [TrivSqZeroExt.fst_mul, TrivSqZeroExt.snd_mul, ha0, hb0]

end LittleFinitistic.PDSquareZero

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Dimension_PDBaseBarConsumer
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.SelectionEncoding.instRingDirectedAlgebra _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAlgebra _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace LittleFinitistic.PDBarQuotient
universe u
variable {k A D : Type u} [Field k] [Ring A] [Algebra k A] [Ring D] [Algebra k D]
variable (f : A →ₐ[k] D)
variable (N : Type u) [AddCommGroup N] [Module k N] [Module A N] [IsScalarTower k A N]
variable [FiniteDimensional k A] [FiniteDimensional k N]

/-- Actual nonzero D-module bar homology, with its exterior action intact,
forces the same projective-dimension lower bound over A. -/
theorem lower_bound_of_base_bar (r n : ℕ) (hrn : r ≤ n)
    (h : ¬ IsZero ((DerivedBar.twoSidedComplex k A D N f).homology n)) :
    r ≤ projectiveDimension (ModuleCat.of A N) := by
  apply PDTensor.lower_bound_of_nonzero_Tor (RightBase f) (PDMinimal.FiniteModule.of (k := k) (A := A) N) r n hrn
  intro hz
  have hz' := hz.of_iso ((torIsoTwoSided f N n) ≪≫
    restrictHomologyIso (DerivedBar.twoSidedComplex k A D N f) n).symm
  apply h
  have hs := (ModuleCat.isZero_iff_subsingleton (R := k)).mp hz'
  exact ModuleCat.isZero_iff_subsingleton.mpr hs

end LittleFinitistic.PDBarQuotient

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Dimension_PDResidueBaseBar
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.countWeight_free _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.term_finite _root_.OAI.DerivedBar.term_finiteDimensional _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.leftModule _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideModule _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.SelectedPDDetection.residueModuleK _root_.OAI.LittleFinitistic.SelectionEncoding.instRingDirectedAlgebra _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option backward.isDefEq.respectTransparency false

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits TensorProduct
open scoped TensorProduct
namespace LittleFinitistic.PDResidueAssociativity
universe u
variable {k A D : Type u} [Field k] [Ring A] [Algebra k A] [Ring D] [Algebra k D]

variable (f : A →ₐ[k] D)
variable (V : Type u) [AddCommGroup V] [Module k V] [Module A V] [IsScalarTower k A V]
local notation "S" => PDTensor.Residue (A := D)

variable {V} {W : Type u} [AddCommGroup W] [Module k W] [Module A W] [IsScalarTower k A W]

variable (N : Type u) [AddCommGroup N] [Module k N] [Module A N] [IsScalarTower k A N]

variable (hf : Function.Surjective f)
variable (hsq : ∀ a ∈ RingHom.ker f.toRingHom, ∀ b ∈ RingHom.ker f.toRingHom, a*b=0)

/-- The actual D-bar has projective terms, even when its length is infinite. -/
theorem twoSided_projective (n : ℕ) : Projective ((DerivedBar.twoSidedComplex k A D N f).X n) := by
  have : Module.Free D (D ⊗[k] DerivedBar.term k A N n) :=
    Module.Free.of_basis (Algebra.TensorProduct.basis D (Module.Free.chooseBasis k (DerivedBar.term k A N n)))
  change Projective (ModuleCat.of D (D ⊗[k] DerivedBar.term k A N n))
  infer_instance

include hf hsq

variable [FiniteDimensional k A] [FiniteDimensional k N]

/-- Bounded D-derived bar homology suffices for finite pd over A. The
exact-tail theorem supplies the amplitude after residue tensor. -/
theorem finite_pd_of_bounded_base_bar (g : ℕ) (hg : ∀ M : ModuleCat.{u} D, HasProjectiveDimensionLE M g)
    (h : ∃ b : ℕ, ∀ n, b < n → IsZero ((DerivedBar.twoSidedComplex k A D N f).homology n)) :
    projectiveDimension (ModuleCat.of A N) < ⊤ := by
  apply PDTensor.projectiveDimension_lt_top_of_bounded_residueTor (PDMinimal.FiniteModule.of (k := k) (A := A) N)
  obtain ⟨b,hb⟩ := h
  refine ⟨b+g+3, fun n hn => ?_⟩
  have he : ∀ i, b+1 ≤ i → (DerivedBar.twoSidedComplex k A D N f).ExactAt i := by
    intro i hi
    exact ((DerivedBar.twoSidedComplex k A D N f).exactAt_iff_isZero_homology i).mpr (hb i (by omega))
  have ht := DerivedBar.ProjectiveTail.map_exact_tail (DerivedBar.twoSidedComplex k A D N f)
    (PDTensor.tensorFunctor k D S) (b+1) g he (twoSided_projective f N) hg n (by omega)
  exact ht.isZero_homology.of_iso (residueTorIso f N hf hsq n)

end LittleFinitistic.PDResidueAssociativity

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Encoding_DirectedBound
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.SelectionEncoding.instRingDirectedAlgebra _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open scoped TensorProduct
open TensorProduct
namespace LittleFinitistic.DirectedBound
universe u v
variable {k A : Type u} [Field k] [Ring A] [Algebra k A] {n : ℕ}

namespace DirectedSystem
variable (D : DirectedSystem k A n)
variable (M : Type v) [AddCommGroup M] [Module A M] [Module k M]
  [IsScalarTower k A M]

open CategoryTheory

include D

/-- Both sides, quantified over arbitrary modules in any larger universe. -/
theorem both_sides_projectiveDimension_le :
    (∀ N : ModuleCat.{max u v} A, projectiveDimension N ≤ (n - 1 : ℕ)) ∧
    (∀ N : ModuleCat.{max u v} Aᵐᵒᵖ, projectiveDimension N ≤ (n - 1 : ℕ)) :=
  ⟨D.all_modules_projectiveDimension_le, D.opposite.all_modules_projectiveDimension_le⟩

end DirectedSystem

open CategoryTheory
end LittleFinitistic.DirectedBound

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Iteration_BinomialVanishing
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticPresentation.instFiniteAuxiliaryEquation _root_.OAI.LittleFinitistic.QuadraticPresentation.instFiniteAuxiliaryLetter _root_.OAI.LittleFinitistic.QuadraticPresentation.step_finite _root_.OAI.LittleFinitistic.QuadraticPresentation.word_finite _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated _root_.OAI.LittleFinitistic.cyclicRing_finiteInst
attribute [-simp] _root_.OAI.ExternalTensor.Section4.sum_hom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open CategoryTheory CategoryTheory.Limits
noncomputable section
namespace ExternalTensor.Binomial
universe v u w
variable {C : Type u} [Category.{v} C] [Preadditive C]

/-- A finite biproduct is zero exactly when all its summands are zero. -/
theorem isZero_biproduct_iff [HasFiniteBiproducts C] {I : Type} [Fintype I] (f : I → C) :
    IsZero (⨁ f) ↔ ∀ i, IsZero (f i) := by
  constructor
  · intro h i
    exact IsZero.of_mono (biproduct.ι f i) h
  · intro h
    apply (IsZero.iff_id_eq_zero _).mpr
    apply biproduct.hom_ext
    intro i
    exact (h i).eq_of_tgt _ _

variable [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]

/-- Integer shifts preserve and reflect the zero object. -/
theorem isZero_shift_iff (X : C) (n : ℤ) : IsZero (X⟦n⟧) ↔ IsZero X := by
  constructor
  · exact IsZero.of_full_of_faithful_of_isZero (shiftFunctor C n) X
  · intro h
    apply (IsZero.iff_id_eq_zero _).mpr
    rw [← (shiftFunctor C n).map_id, h.eq_zero_of_src (𝟙 X), Functor.map_zero]

variable [HasFiniteBiproducts C]

/-- The q=0 summand always occurs once, so the binomial expansion detects zero. -/
theorem binomialObject_isZero_iff (b d : ℤ) (j : ℕ) (X : C) :
    IsZero (binomialObject b d j X) ↔ IsZero X := by
  unfold binomialObject
  rw [isZero_biproduct_iff]
  simp only [isZero_biproduct_iff, isZero_shift_iff]
  constructor
  · intro h
    exact h ⟨0, Nat.succ_pos j⟩ ⟨0, by simp⟩
  · intro h _ _
    exact h

variable [HasBinaryBiproducts C]
variable {S : Type w} (Phi : C ⥤ C) [Phi.Additive] [Phi.CommShift ℤ]
  (M : S → C) (H : S → S) (b d : ℤ)

/-- Exact zero detection for the iterates; no faithfulness of M is silently assumed. -/
theorem iteration_isZero_iff
    (split : ∀ Y, Phi.obj (M Y) ≅ (M (H Y))⟦b⟧ ⊞ (M (H Y))⟦b+d⟧)
    (j : ℕ) (Y : S) :
    IsZero ((Phi.obj^[j]) (M Y)) ↔ IsZero (M ((H^[j]) Y)) :=
  (binomialIteration Phi M H b d split j Y).isZero_iff.trans
    (binomialObject_isZero_iff b d j _)

end ExternalTensor.Binomial

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Iteration_IntegerIterateAmplitude
attribute [-instance] _root_.OAI.DerivedBar.countComplex_projective _root_.OAI.DerivedBar.countSum_projective _root_.OAI.DerivedBar.integerCountSum_isKProjective _root_.OAI.DerivedBar.integerCount_isKProjective _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleTotal.augmentationComparisonOnChains_isIso _root_.OAI.LittleFinitistic.BimoduleTotal.resolvedTensorAugmentation_isIso _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.OrdinarySimulation.TensorResolution.projectiveTerm _root_.OAI.LittleFinitistic.PDMinimal.term_projective _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.SelectionEncoding.instRingDirectedAlgebra _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
attribute [-simp] _root_.OAI.ExternalTensor.Section4.sum_hom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex
namespace DerivedBar.IterateSupport
universe u
variable (k D X : Type u) [Field k] [Ring D] [Algebra k D]
  [AddCommGroup X] [Module k X] [Module D X] [Module Dᵐᵒᵖ X]
  [IsScalarTower k D X]
variable (g : ℕ) (hg : ∀ M : ModuleCat.{u} D, HasProjectiveDimensionLE M g)
variable (N : ModuleCat.{u} D)

include hg in
/-- A bounded input remains cohomologically bounded after actual derived tensor.
The input is resolved by its genuine projective bar total. -/
theorem tensor_exact_above (Z : ChainComplex (ModuleCat.{u} D) ℕ) (m : ℕ)
    (hZ : ∀ i, m < i → Z.ExactAt i) (n : ℕ) (hn : m+g+2 < n) :
    ((tensorTotalFunctor k D X).obj Z).ExactAt n := by
  apply ProjectiveTail.map_exact_tail (barTotal k D Z) (BimoduleTensor.tensorFunctor k D X)
    (m+1) g
  · intro i hi
    exact (exactAt_iff_of_quasiIsoAt (barTotalAugmentation k D Z) i).mpr (hZ i (by omega))
  · exact barTotal_projective k D Z
  · exact hg
  · omega

include hg in
/-- The actual finite iteration has an explicit finite homological support bound.
This bound has a two-degree allowance per step; no optimal upper bound is claimed. -/
theorem resolvedModel_exact_above (r n : ℕ) (hn : r*(g+2) < n) :
    (resolvedModel k D X N r).ExactAt n := by
  induction r generalizing n with
  | zero =>
    cases n with
    | zero => simp at hn
    | succ n => exact ChainComplex.exactAt_succ_single_obj _ _
  | succ r ih =>
    apply tensor_exact_above k D X g hg (resolvedModel k D X N r) (r*(g+2)) ih n
    simpa only [Nat.add_mul, Nat.one_mul, Nat.add_assoc] using hn

attribute [local instance] OAI.DerivedBar.IterateSupport.instHasDerivedCategoryModuleCat_solutions_2
include hg in
/-- Actual derived tensor iterates have finite lower cohomological support over
any ring with the supplied genuine global projective-dimension bound. -/
theorem isGE_bound (r : ℕ) : (object k D X N r).IsGE (-((r*(g+2) : ℕ) : ℤ)) := by
  apply (DerivedCategory.isGE_iff _ _).mpr
  intro i hi
  obtain ⟨n,rfl⟩ := Int.exists_eq_neg_ofNat (show i ≤ 0 by omega)
  let e := (DerivedCategory.homologyFunctor (ModuleCat D) (-(n : ℤ))).mapIso
    (resolvedModelIso k D X N r) ≪≫
    (DerivedCategory.homologyFunctorFactors (ModuleCat D) (-(n : ℤ))).app
      ((integerExtension D).obj (resolvedModel k D X N r)) ≪≫
    integerExtensionHomologyIso D (resolvedModel k D X N r) n
  exact e.isZero_iff.mpr ((resolvedModel_exact_above k D X g hg N r n (by omega)).isZero_homology)

variable [SMulCommClass D Dᵐᵒᵖ X] [IsScalarTower k Dᵐᵒᵖ X]

include hg in
theorem bounded_amplitude (r : ℕ) :
    (object k D X N r).IsGE (-((r*(g+2) : ℕ) : ℤ)) ∧ (object k D X N r).IsLE 0 :=
  ⟨isGE_bound k D X g hg N r, inferInstance⟩
end DerivedBar.IterateSupport

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Iteration_IntegerIterateExtinction
attribute [-instance] _root_.OAI.DerivedBar.countWeight_free _root_.OAI.DerivedBar.integerCountSum_isKProjective _root_.OAI.DerivedBar.integerCount_isKProjective _root_.OAI.DerivedBar.term_finite _root_.OAI.DerivedBar.term_finiteDimensional _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideModule _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleTotal.augmentationComparisonOnChains_isIso _root_.OAI.LittleFinitistic.BimoduleTotal.barInputAugmentation_isIso _root_.OAI.LittleFinitistic.BimoduleTotal.resolvedTensorAugmentation_isIso _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.SelectedFirstBlockFamily.derivedInflation_additive _root_.OAI.LittleFinitistic.SelectionEncoding.instRingDirectedAlgebra _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
attribute [-simp] _root_.OAI.DerivedBar.ParityBridge.baseEmbed_tmul _root_.OAI.DerivedBar.ParityBridge.canonicalLinear_apply _root_.OAI.DerivedBar.ParityBridge.idealEmbed_tmul _root_.OAI.DerivedBar.ParityBridge.idealSuffixEmbed_tmul _root_.OAI.DerivedBar.ParityBridge.innerEmbedding_lof_succ _root_.OAI.DerivedBar.ParityBridge.outerCast_refl _root_.OAI.DerivedBar.ParityBridge.outerSuffixEmbed_tmul _root_.OAI.DerivedBar.ParityBridge.suffixEmbed_tmul _root_.OAI.DerivedBar.ParityBridge.termCast_refl _root_.OAI.DerivedBar.SquareZero.multibarAugmentedDifferential_zero _root_.OAI.ExternalTensor.Section4.sum_hom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex ZeroObject
namespace DerivedBar.IterateSupport
universe u
variable (k D X : Type u) [Field k] [Ring D] [Algebra k D]
  [AddCommGroup X] [Module k X] [Module D X] [Module Dᵐᵒᵖ X]
  [SMulCommClass D Dᵐᵒᵖ X] [IsScalarTower k D X] [IsScalarTower k Dᵐᵒᵖ X]

attribute [local instance] OAI.DerivedBar.IterateSupport.integerIterateExtinctionHasDerivedCategory
/-- The integer derived object of an actual nonnegative chain complex vanishes
exactly when the original chain complex is exact in every degree. -/
theorem integerQ_isZero_iff (Z : ChainComplex (ModuleCat.{u} D) ℕ) :
    IsZero ((integerQ D).obj Z) ↔ ∀ n, Z.ExactAt n := by
  constructor
  · intro h n
    apply (exactAt_iff_isZero_homology _ _).mpr
    have hz := (DerivedCategory.homologyFunctor (ModuleCat D) (-(n : ℤ))).map_isZero h
    exact ((DerivedCategory.homologyFunctorFactors (ModuleCat D) (-(n : ℤ))).app
      ((integerExtension D).obj Z) ≪≫ integerExtensionHomologyIso D Z n).isZero_iff.mp hz
  · intro h
    have : ((integerExtension D).obj Z).IsStrictlyLE 0 := by
      exact inferInstanceAs (CochainComplex.IsStrictlyLE
        (Z.extend ComplexShape.embeddingDownNat) 0)
    have : ((integerQ D).obj Z).IsLE 0 := by
      change (DerivedCategory.Q.obj ((integerExtension D).obj Z)).IsLE 0
      infer_instance
    have hz (i : ℤ) : IsZero ((DerivedCategory.homologyFunctor (ModuleCat D) i).obj
        ((integerQ D).obj Z)) := by
      by_cases hi : i ≤ 0
      · obtain ⟨n,rfl⟩ := Int.exists_eq_neg_ofNat hi
        exact ((DerivedCategory.homologyFunctorFactors (ModuleCat D) (-(n : ℤ))).app
          ((integerExtension D).obj Z) ≪≫ integerExtensionHomologyIso D Z n).isZero_iff.mpr
            ((exactAt_iff_isZero_homology _ _).mp (h n))
      · exact DerivedCategory.isZero_of_isLE _ 0 i (by omega)
    have : ((integerQ D).obj Z).IsLE (-1) :=
      (DerivedCategory.isLE_iff _ _).mpr (fun i _ => hz i)
    have : ((integerQ D).obj Z).IsGE 0 :=
      (DerivedCategory.isGE_iff _ _).mpr (fun i _ => hz i)
    apply (IsZero.iff_id_eq_zero _).mpr
    exact DerivedCategory.TStructure.t.zero (𝟙 _) (-1) 0 (by omega)

local instance instPreservesZeroMorphismsChainComplexModuleCatNatBarTotalFunctor : (barTotalFunctor k D).PreservesZeroMorphisms where
  map_zero Z W := by
    apply HomologicalComplex.Hom.ext
    funext n
    apply HomologicalComplex₂.total.hom_ext (K := barBicomplex k D Z)
    intro i q h
    erw [ι_barTotalFunctor_map k D (0 : Z ⟶ W) i q n h]
    simp [termMap_zero]
    erw [zero_comp,comp_zero]
    rfl
local instance instPreservesZeroMorphismsChainComplexModuleCatNatTensorTotalFunctor : (tensorTotalFunctor k D X).PreservesZeroMorphisms := by
  dsimp [tensorTotalFunctor]
  infer_instance

omit [SMulCommClass D Dᵐᵒᵖ X] [IsScalarTower k Dᵐᵒᵖ X]
/-- The actual resolve-and-tensor functor sends an acyclic chain input to an acyclic output. -/
theorem tensor_acyclic (Z : ChainComplex (ModuleCat.{u} D) ℕ)
    (h : ∀ n, Z.ExactAt n) : ∀ n, ((tensorTotalFunctor k D X).obj Z).ExactAt n := by
  let f : Z ⟶ 0 := 0
  have : QuasiIso f := ⟨fun n => (quasiIsoAt_iff_exactAt f n (h n)).mpr
    ((exactAt_iff_isZero_homology _ _).mpr
      ((HomologicalComplex.homologyFunctor _ (.down ℕ) n).map_isZero (Limits.isZero_zero _)))⟩
  let G := tensorTotalFunctor k D X
  have hz := G.map_isZero (Limits.isZero_zero (ChainComplex (ModuleCat.{u} D) ℕ))
  intro n
  apply (exactAt_iff_of_quasiIsoAt (G.map f) n).mpr
  exact (exactAt_iff_isZero_homology _ _).mpr
    ((HomologicalComplex.homologyFunctor _ (.down ℕ) n).map_isZero hz)

variable (N : ModuleCat.{u} D)

/-- Extinction is permanent for the genuine bar-derived iteration. -/
theorem zero_succ (r : ℕ) (h : IsZero (object k D X N r)) :
    IsZero (object k D X N (r+1)) := by
  apply (resolvedModelIso k D X N (r+1)).isZero_iff.mpr
  apply (integerQ_isZero_iff (D := D) (resolvedModel k D X N (r+1))).mpr
  apply tensor_acyclic k D X (resolvedModel k D X N r)
  exact (integerQ_isZero_iff (D := D) (resolvedModel k D X N r)).mp
    ((resolvedModelIso k D X N r).isZero_iff.mp h)

/-- A proved zero iterate kills every later iterate, without a native-functor comparison premise. -/
theorem zero_of_le (t r : ℕ) (htr : t ≤ r) (h : IsZero (object k D X N t)) :
    IsZero (object k D X N r) := by
  induction r, htr using Nat.le_induction with
  | base => exact h
  | succ r _ ih => exact zero_succ k D X N r ih
end DerivedBar.IterateSupport

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Ordinary_OrdinaryBlockBimodule
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideModule _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.OrdinarySimulation.BimoduleO.commuteRightTensor _root_.OAI.LittleFinitistic.OrdinarySimulation.TensorResolution.augmentation_epi _root_.OAI.LittleFinitistic.OrdinarySimulation.VertexTensor.instAddCommGroup _root_.OAI.LittleFinitistic.OrdinarySimulation.VertexTensor.instIsScalarTowerEnveloping _root_.OAI.LittleFinitistic.OrdinarySimulation.VertexTensor.instModule _root_.OAI.LittleFinitistic.OrdinarySimulation.VertexTensor.instModuleEnveloping _root_.OAI.LittleFinitistic.OrdinarySimulation.XResolution.rightTerm_projective _root_.OAI.LittleFinitistic.OrdinarySimulation.shifted_right_projective _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.SelectedOrdinaryAlgebra.term_finite _root_.OAI.LittleFinitistic.SelectedOrdinaryModules.instFiniteAInflated _root_.OAI.LittleFinitistic.SelectedOrdinaryModules.instIsScalarTowerComplexAInflated _root_.OAI.LittleFinitistic.SelectedOrdinaryModules.instModuleAInflated _root_.OAI.LittleFinitistic.SelectedPDDetection.residueModuleK _root_.OAI.LittleFinitistic.SelectionEncoding.instRingDirectedAlgebra _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
namespace LittleFinitistic.OrdinarySimulation
universe u
variable {k L R O T : Type u} [Field k] [Ring L] [Ring R]
  [AddCommGroup O] [AddCommGroup T]

open CategoryTheory
open scoped TensorProduct
variable {B : Type u} [Ring B] [Algebra k B]

theorem ordinary_finite (P : CochainComplex (ModuleCat.{u} (Enveloping k B)) ℤ)
    (a : ℤ) (l : ℕ) [FiniteDimensional k B]
    [∀ n, FiniteDimensional k ((underlyingComplex (k := k) P).X n)] :
    FiniteDimensional k (BimoduleX P a l) := inferInstance
end LittleFinitistic.OrdinarySimulation

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Ordinary_OrdinaryProductSecondDimension
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideModule _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.BlockModule.derivedFirstIso_hom_commShift _root_.OAI.LittleFinitistic.BlockModule.derivedFirstIso_inv_commShift _root_.OAI.LittleFinitistic.BlockModule.firstInflation_preservesFiniteColimits _root_.OAI.LittleFinitistic.BlockModule.firstInflation_preservesFiniteLimits _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.SelectionEncoding.instRingDirectedAlgebra _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory
namespace LittleFinitistic.ProductModules
universe u v
variable (L R : Type u) [Ring L] [Ring R]

attribute [local instance] RingHomInvPair.of_ringEquiv

variable [Small.{v} L] [Small.{v} R]

/-- Each module over the product has the same finite bound as its two factors. -/
theorem product_module_bound (n : ℕ)
    (hL : ∀ M : ModuleCat.{v} L, projectiveDimension M ≤ (n : ℕ))
    (hR : ∀ M : ModuleCat.{v} R, projectiveDimension M ≤ (n : ℕ))
    (M : ModuleCat.{v} (L × R)) : projectiveDimension M ≤ (n : ℕ) := by
  have : HasProjectiveDimensionLE (firstObject L R M) n := (projectiveDimension_le_iff _ n).mp (hL _)
  have : HasProjectiveDimensionLE (secondObject L R M) n := (projectiveDimension_le_iff _ n).mp (hR _)
  have := firstInflation_dimensionLE L R n (firstObject L R M)
  have := secondInflation_dimensionLE L R n (secondObject L R M)
  let e := ModuleCat.biprodIsoProd ((firstInflation L R).obj (firstObject L R M))
    ((secondInflation L R).obj (secondObject L R M))
  have : HasProjectiveDimensionLT (pairObject L R M) (n+1) := hasProjectiveDimensionLT_of_iso e (n+1)
  have : HasProjectiveDimensionLT M (n+1) :=
    hasProjectiveDimensionLT_of_iso (splitting L R M).toModuleIso.symm (n+1)
  exact (projectiveDimension_le_iff _ n).mpr inferInstance
end LittleFinitistic.ProductModules

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Ordinary_OrdinaryProductOpposite
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.SelectionEncoding.instRingDirectedAlgebra _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory
namespace LittleFinitistic.ProductModules
universe u v
variable (L R : Type u) [Ring L] [Ring R]

attribute [local instance] RingHomInvPair.of_ringEquiv

variable [Small.{v} L] [Small.{v} R]

theorem opposite_product_module_bound (n : ℕ)
    (hL : ∀ M : ModuleCat.{v} Lᵐᵒᵖ, projectiveDimension M ≤ (n : ℕ))
    (hR : ∀ M : ModuleCat.{v} Rᵐᵒᵖ, projectiveDimension M ≤ (n : ℕ))
    (M : ModuleCat.{v} (L × R)ᵐᵒᵖ) : projectiveDimension M ≤ (n : ℕ) := by
  let : Small.{v} Lᵐᵒᵖ := small_of_injective (@MulOpposite.unop_injective L)
  let : Small.{v} Rᵐᵒᵖ := small_of_injective (@MulOpposite.unop_injective R)
  let : Small.{v} (L × R)ᵐᵒᵖ := small_of_injective (@MulOpposite.unop_injective (L × R))
  rw [ModuleCat.projectiveDimension_eq_of_semiLinearEquiv (oppositeEquiv L R) (oppositeModuleEquiv L R M)]
  exact product_module_bound Lᵐᵒᵖ Rᵐᵒᵖ n hL hR (oppositeModule L R M)
end LittleFinitistic.ProductModules

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Ordinary_OrdinaryFirstDerivedRetraction
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.SelectedFirstBlockFamily.derivedInflation_additive _root_.OAI.LittleFinitistic.SelectedFirstBlockFamily.inflation_preservesFiniteColimits _root_.OAI.LittleFinitistic.SelectedFirstBlockFamily.inflation_preservesFiniteLimits _root_.OAI.LittleFinitistic.SelectionEncoding.instRingDirectedAlgebra _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace LittleFinitistic.BlockModule
universe u
variable (L R : Type u) [Ring L] [Ring R]
variable [HasDerivedCategory.{u+1} (ModuleCat.{u} L)]
variable [HasDerivedCategory.{u+1} (ModuleCat.{u} (L × R))]

/-- No derived object becomes zero merely by putting it in the first block. -/
theorem derivedFirst_isZero_iff (Y : DerivedCategory (ModuleCat.{u} L)) :
    IsZero ((derivedFirst L R).obj Y) ↔ IsZero Y := by
  constructor
  · intro h
    exact ((derivedFirstRetraction L R).app Y).isZero_iff.mp
      ((derivedFirstComponent L R).map_isZero h)
  · exact (derivedFirst L R).map_isZero

end LittleFinitistic.BlockModule

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Selection_GroupSelection
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FiniteSelectionFamily.ringModule _root_.OAI.LittleFinitistic.FiniteSelectionFamily.tower _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.SelectedBaseIterates.input_finite _root_.OAI.LittleFinitistic.SelectedBaseIterates.input_finiteD _root_.OAI.LittleFinitistic.SelectedFirstBlockFamily.derivedInflation_additive _root_.OAI.LittleFinitistic.SelectedFirstBlockFamily.inflation_preservesFiniteColimits _root_.OAI.LittleFinitistic.SelectedFirstBlockFamily.inflation_preservesFiniteLimits _root_.OAI.LittleFinitistic.SelectedNativeEvaluation.instFiniteDimensionalComplexCarrierH _root_.OAI.LittleFinitistic.SelectedOrdinaryAlgebra.D_finite _root_.OAI.LittleFinitistic.SelectedOrdinaryAlgebra.base_finite _root_.OAI.LittleFinitistic.SelectedOrdinaryAlgebra.term_finite _root_.OAI.LittleFinitistic.SelectedOrdinaryAlgebra.term_projective _root_.OAI.LittleFinitistic.SelectedOrdinaryModules.instFiniteAInflated _root_.OAI.LittleFinitistic.SelectedOrdinaryModules.instIsScalarTowerComplexAInflated _root_.OAI.LittleFinitistic.SelectedOrdinaryModules.instIsScalarTowerComplexBPInflated _root_.OAI.LittleFinitistic.SelectedOrdinaryModules.instIsScalarTowerComplexDInflated _root_.OAI.LittleFinitistic.SelectedOrdinaryModules.instModuleAInflated _root_.OAI.LittleFinitistic.SelectedOrdinaryModules.instModuleBComplexPInflated _root_.OAI.LittleFinitistic.SelectedOrdinaryModules.instModuleDInflated _root_.OAI.LittleFinitistic.SelectedPDDetection.residueModuleK _root_.OAI.LittleFinitistic.SelectedTensor.comparison_isIso _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated _root_.OAI.LittleFinitistic.testModule_module _root_.OAI.LittleFinitistic.testModule_scalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Group identities used in Section 2 of v5s9.15. -/

open scoped commutatorElement

namespace LittleFinitistic

namespace Presentation

theorem shiftAut_z (k N : ℤ) : shiftAut k (z N) = z (N+k) := by
  change shiftHom k ⁅data.U 0 0,data.V 0 N⁆ = data.centralZ (N+k)
  rw [map_commutatorElement,shiftHom_U,shiftHom_V,zero_add]
  exact (data.centralZ_eq (N+k) 0 k N (by omega)).symm

end Presentation

end LittleFinitistic

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Selection_SelectionAlgebra
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FiniteSelectionFamily.ringModule _root_.OAI.LittleFinitistic.FiniteSelectionFamily.tower _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.SelectedBaseIterates.input_finite _root_.OAI.LittleFinitistic.SelectedBaseIterates.input_finiteD _root_.OAI.LittleFinitistic.SelectedFirstBlockFamily.derivedInflation_additive _root_.OAI.LittleFinitistic.SelectedFirstBlockFamily.inflation_preservesFiniteColimits _root_.OAI.LittleFinitistic.SelectedFirstBlockFamily.inflation_preservesFiniteLimits _root_.OAI.LittleFinitistic.SelectedNativeEvaluation.instFiniteDimensionalComplexCarrierH _root_.OAI.LittleFinitistic.SelectedOrdinaryAlgebra.D_finite _root_.OAI.LittleFinitistic.SelectedOrdinaryAlgebra.base_finite _root_.OAI.LittleFinitistic.SelectedOrdinaryAlgebra.term_finite _root_.OAI.LittleFinitistic.SelectedOrdinaryAlgebra.term_projective _root_.OAI.LittleFinitistic.SelectedOrdinaryModules.instFiniteAInflated _root_.OAI.LittleFinitistic.SelectedOrdinaryModules.instIsScalarTowerComplexAInflated _root_.OAI.LittleFinitistic.SelectedOrdinaryModules.instIsScalarTowerComplexBPInflated _root_.OAI.LittleFinitistic.SelectedOrdinaryModules.instIsScalarTowerComplexDInflated _root_.OAI.LittleFinitistic.SelectedOrdinaryModules.instModuleAInflated _root_.OAI.LittleFinitistic.SelectedOrdinaryModules.instModuleBComplexPInflated _root_.OAI.LittleFinitistic.SelectedOrdinaryModules.instModuleDInflated _root_.OAI.LittleFinitistic.SelectedPDDetection.residueModuleK _root_.OAI.LittleFinitistic.SelectedTensor.comparison_isIso _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated _root_.OAI.LittleFinitistic.testModule_module _root_.OAI.LittleFinitistic.testModule_scalarTower
attribute [-simp] _root_.OAI.ExternalTensor.Section4.sum_hom _root_.OAI.LittleFinitistic.FinitePresentation.fromModel_T _root_.OAI.LittleFinitistic.FinitePresentation.fromModel_u _root_.OAI.LittleFinitistic.FinitePresentation.fromModel_v _root_.OAI.LittleFinitistic.FinitePresentation.fromModel_w _root_.OAI.LittleFinitistic.FinitePresentation.toModel_T _root_.OAI.LittleFinitistic.FinitePresentation.toModel_U _root_.OAI.LittleFinitistic.FinitePresentation.toModel_V _root_.OAI.LittleFinitistic.FinitePresentation.toModel_W _root_.OAI.LittleFinitistic.testModule_smul_val _root_.OAI.LittleFinitistic.testRingMap_algebraZ
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
namespace LittleFinitistic

open MonoidAlgebra

@[simp] theorem selectionAutomorphism_z (k q : ℤ) :
    selectionAutomorphism k (algebraZ q) = algebraZ (q+k) := by
  simp [selectionAutomorphism,algebraZ,Presentation.shiftAut_z]

@[simp] theorem selectionAutomorphism_idempotent (k q : ℤ) :
    selectionAutomorphism k (selectionIdempotent q) = selectionIdempotent (q+k) := by
  simp [selectionIdempotent]

end LittleFinitistic

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Selection_FiniteQuotient
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.SelectionEncoding.instRingDirectedAlgebra _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated _root_.OAI.LittleFinitistic.cyclicRing_charTwo _root_.OAI.LittleFinitistic.cyclicRing_finiteInst _root_.OAI.LittleFinitistic.cyclicRing_nontrivial _root_.OAI.LittleFinitistic.finiteQuotientGroup_finite _root_.OAI.LittleFinitistic.testModule_finiteDimensional _root_.OAI.LittleFinitistic.testModule_module _root_.OAI.LittleFinitistic.testModule_scalarTower
attribute [-simp] _root_.OAI.ExternalTensor.Section4.sum_hom _root_.OAI.LittleFinitistic.cyclicUnit_val _root_.OAI.LittleFinitistic.testModule_smul_val _root_.OAI.LittleFinitistic.testRingMap_algebraZ
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-!
Exact prerequisites for Section 2 of v5s9.15.

These are the variable-coefficient elementary-matrix calculations in the
finite-quotient construction, over the actual rings F₂[t]/(t^m - 1).
They do not establish the paper's main homological theorem.
-/

open Matrix Polynomial

namespace LittleFinitistic

section ElementaryMatrices

variable {R : Type*} [CommRing R]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] in
theorem transvection_injective (i j : ι) (hij : i ≠ j) :
    Function.Injective (transvection (R := R) i j) := by
  intro a b h
  have := congrArg (fun M : Matrix ι ι R => M i j) h
  simpa [transvection, Matrix.single, Matrix.one_apply, hij] using this

end ElementaryMatrices

theorem cyclicBasis_apply (m : ℕ) (hm : m ≠ 0) (i : Fin m) :
    cyclicBasis m hm i = AdjoinRoot.root (cyclicPolynomial m) ^ (i : ℕ) := by
  simp only [cyclicBasis, Module.Basis.reindex_apply, PowerBasis.basis_eq_pow,
    AdjoinRoot.powerBasis'_gen]
  rfl

theorem cyclic_powers_independent (m : ℕ) (hm : m ≠ 0) :
    LinearIndependent (ZMod 2)
      (fun i : Fin m => AdjoinRoot.root (cyclicPolynomial m) ^ (i : ℕ)) := by
  have h : (fun i : Fin m => cyclicBasis m hm i) =
      (fun i : Fin m => AdjoinRoot.root (cyclicPolynomial m) ^ (i : ℕ)) :=
    funext (cyclicBasis_apply m hm)
  rw [← h]
  exact (cyclicBasis m hm).linearIndependent

theorem centralMatrix_injective (m : ℕ) (hm : m ≠ 0) :
    Function.Injective (centralMatrix m) := by
  intro c d h
  have hs := transvection_injective (R := CyclicRing m) (0 : Fin 5) 4 (by decide) h
  have hz : ∑ i : Fin m, (c i - d i) •
      AdjoinRoot.root (cyclicPolynomial m) ^ (i : ℕ) = 0 := by
    simp only [sub_smul, Finset.sum_sub_distrib, hs, sub_self]
  have hc := (linearIndependent_iff'.mp (cyclic_powers_independent m hm))
    Finset.univ (fun i => c i - d i) (by simpa using hz)
  funext i
  exact sub_eq_zero.mp (hc i (Finset.mem_univ i))

theorem centralEmbedding_injective (m : ℕ) (hm : m ≠ 0) :
    Function.Injective (centralEmbedding m) := by
  intro c d h
  exact (centralMatrix_injective m hm) (congrArg Units.val h)

end LittleFinitistic

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Selection_MatrixModel
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FiniteSelectionFamily.ringModule _root_.OAI.LittleFinitistic.FiniteSelectionFamily.tower _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.SelectedBaseIterates.input_finite _root_.OAI.LittleFinitistic.SelectedBaseIterates.input_finiteD _root_.OAI.LittleFinitistic.SelectedFirstBlockFamily.derivedInflation_additive _root_.OAI.LittleFinitistic.SelectedFirstBlockFamily.inflation_preservesFiniteColimits _root_.OAI.LittleFinitistic.SelectedFirstBlockFamily.inflation_preservesFiniteLimits _root_.OAI.LittleFinitistic.SelectedNativeEvaluation.instFiniteDimensionalComplexCarrierH _root_.OAI.LittleFinitistic.SelectedOrdinaryAlgebra.D_finite _root_.OAI.LittleFinitistic.SelectedOrdinaryAlgebra.base_finite _root_.OAI.LittleFinitistic.SelectedOrdinaryAlgebra.term_finite _root_.OAI.LittleFinitistic.SelectedOrdinaryAlgebra.term_projective _root_.OAI.LittleFinitistic.SelectedOrdinaryModules.instFiniteAInflated _root_.OAI.LittleFinitistic.SelectedOrdinaryModules.instIsScalarTowerComplexAInflated _root_.OAI.LittleFinitistic.SelectedOrdinaryModules.instIsScalarTowerComplexBPInflated _root_.OAI.LittleFinitistic.SelectedOrdinaryModules.instIsScalarTowerComplexDInflated _root_.OAI.LittleFinitistic.SelectedOrdinaryModules.instModuleAInflated _root_.OAI.LittleFinitistic.SelectedOrdinaryModules.instModuleBComplexPInflated _root_.OAI.LittleFinitistic.SelectedOrdinaryModules.instModuleDInflated _root_.OAI.LittleFinitistic.SelectedPDDetection.residueModuleK _root_.OAI.LittleFinitistic.SelectedTensor.comparison_isIso _root_.OAI.LittleFinitistic.SelectionEncoding.instRingDirectedAlgebra _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated _root_.OAI.LittleFinitistic.testModule_finiteDimensional _root_.OAI.LittleFinitistic.testModule_module _root_.OAI.LittleFinitistic.testModule_scalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open scoped commutatorElement

namespace LittleFinitistic

theorem quotientCentralEmbedding_injective (m : ℕ) [NeZero m] :
    Function.Injective (quotientCentralEmbedding m) := by
  intro a b h
  exact centralEmbedding_injective m (NeZero.ne m) (congrArg Subtype.val h)

theorem quotientCentralEmbedding_basis (m : ℕ) [NeZero m] (i : Fin m) :
    quotientCentralEmbedding m (Multiplicative.ofAdd (Pi.single i 1)) =
      finiteQuotientMap m (Presentation.z i.val) :=
  Subtype.ext (centralEmbedding_basis m i)

end LittleFinitistic

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Selection_CharacterModule
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
attribute [-simp] _root_.OAI.ExternalTensor.Section4.sum_hom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open scoped BigOperators

namespace LittleFinitistic
namespace CharacterModule

open MonoidAlgebra

variable {H F : Type*} [Group H] [Group F] [Fintype H]
variable (ψ : H →* F) (χ : H →* ℂˣ)

theorem projector_coeff_one (hψ : Function.Injective ψ) :
    (projector ψ χ).coeff 1 = 1 := by
  classical
  have hp (h : H) : ψ h = 1 ↔ h = 1 := by
    rw [← map_one ψ]
    exact hψ.eq_iff
  simp [projector, coeff_sum, coeff_single, Finsupp.single_apply, hp]

theorem projector_ne_zero (hψ : Function.Injective ψ) : projector ψ χ ≠ 0 := by
  intro h
  have := projector_coeff_one ψ χ hψ
  rw [h] at this
  simp at this

theorem projector_eigen (h : H) :
    single (ψ h) (1 : ℂ) * projector ψ χ = (χ h : ℂ) • projector ψ χ := by
  classical
  unfold projector
  rw [Finset.mul_sum, Finset.smul_sum]
  have he := Equiv.sum_comp (Equiv.mulLeft h) (fun k : H =>
    (χ h : ℂ) • single (ψ k) ((χ k : ℂ)⁻¹))
  rw [← he]
  apply Finset.sum_congr rfl
  intro k _
  change single (ψ h) (1 : ℂ) * single (ψ k) ((χ k : ℂ)⁻¹) =
    (χ h : ℂ) • single (ψ (h*k)) ((χ (h*k) : ℂ)⁻¹)
  simp only [map_mul,Units.val_mul,single_mul_single,one_mul,
    smul_single,smul_eq_mul]
  congr 1
  field_simp

variable (hc : ∀ h g, Commute (ψ h) g)

theorem projector_mem : projector ψ χ ∈ eigenspace ψ χ hc :=
  projector_eigen ψ χ

theorem eigenspace_nontrivial (hψ : Function.Injective ψ) :
    Nontrivial (eigenspace ψ χ hc) := by
  refine ⟨⟨⟨projector ψ χ,projector_mem ψ χ hc⟩,0,?_⟩⟩
  intro h
  exact projector_ne_zero ψ χ hψ (congrArg Subtype.val h)

end CharacterModule
end LittleFinitistic

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Selection_TestModules
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.DirectedBound.DirectedSystem.cover_addCommGroup _root_.OAI.LittleFinitistic.FiniteSelectionFamily.ringModule _root_.OAI.LittleFinitistic.FiniteSelectionFamily.tower _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.OrdinarySimulation.TensorIdeal.leftModule _root_.OAI.LittleFinitistic.OrdinarySimulation.TensorIdeal.towerLeft _root_.OAI.LittleFinitistic.ProductModules.firstModule _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.SelectedBaseIterates.input_finite _root_.OAI.LittleFinitistic.SelectedBaseIterates.input_finiteD _root_.OAI.LittleFinitistic.SelectedFirstBlockFamily.derivedInflation_additive _root_.OAI.LittleFinitistic.SelectedFirstBlockFamily.inflation_preservesFiniteColimits _root_.OAI.LittleFinitistic.SelectedFirstBlockFamily.inflation_preservesFiniteLimits _root_.OAI.LittleFinitistic.SelectedNativeEvaluation.instFiniteDimensionalComplexCarrierH _root_.OAI.LittleFinitistic.SelectedOrdinaryAlgebra.D_finite _root_.OAI.LittleFinitistic.SelectedOrdinaryAlgebra.base_finite _root_.OAI.LittleFinitistic.SelectedOrdinaryAlgebra.term_finite _root_.OAI.LittleFinitistic.SelectedOrdinaryAlgebra.term_projective _root_.OAI.LittleFinitistic.SelectedOrdinaryModules.instFiniteAInflated _root_.OAI.LittleFinitistic.SelectedOrdinaryModules.instIsScalarTowerComplexAInflated _root_.OAI.LittleFinitistic.SelectedOrdinaryModules.instIsScalarTowerComplexBPInflated _root_.OAI.LittleFinitistic.SelectedOrdinaryModules.instIsScalarTowerComplexDInflated _root_.OAI.LittleFinitistic.SelectedOrdinaryModules.instModuleAInflated _root_.OAI.LittleFinitistic.SelectedOrdinaryModules.instModuleBComplexPInflated _root_.OAI.LittleFinitistic.SelectedOrdinaryModules.instModuleDInflated _root_.OAI.LittleFinitistic.SelectedPDDetection.residueModuleK _root_.OAI.LittleFinitistic.SelectedTensor.comparison_isIso _root_.OAI.LittleFinitistic.SelectionEncoding.instRingDirectedAlgebra _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
attribute [-simp] _root_.OAI.ExternalTensor.Section4.sum_hom _root_.OAI.LittleFinitistic.FinitePresentation.fromModel_T _root_.OAI.LittleFinitistic.FinitePresentation.fromModel_u _root_.OAI.LittleFinitistic.FinitePresentation.fromModel_v _root_.OAI.LittleFinitistic.FinitePresentation.fromModel_w _root_.OAI.LittleFinitistic.FinitePresentation.toModel_T _root_.OAI.LittleFinitistic.FinitePresentation.toModel_U _root_.OAI.LittleFinitistic.FinitePresentation.toModel_V _root_.OAI.LittleFinitistic.FinitePresentation.toModel_W
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
namespace LittleFinitistic
open MonoidAlgebra

noncomputable instance testModule_nontrivial (m : ℕ) [NeZero m] : Nontrivial (TestModule m) :=
  CharacterModule.eigenspace_nontrivial _ _ _ (quotientCentralEmbedding_injective m)

theorem testModule_basis_action (m : ℕ) [NeZero m] (i : Fin m) (x : TestModule m) :
    algebraZ i.val • x = (if i = lastIndex m then (-1 : ℂ) else 1) • x := by
  apply Subtype.ext
  change testRingMap m (algebraZ i.val) * x.val = _
  rw [testRingMap_algebraZ,← quotientCentralEmbedding_basis]
  have hx := x.property (Multiplicative.ofAdd (Pi.single i 1))
  rw [selectionCharacter_basis] at hx
  by_cases h : i = lastIndex m
  · simp only [h,ite_true, if_true,Units.val_neg,Units.val_one] at hx ⊢
    exact hx
  · simp only [h,ite_false, if_false,Units.val_one] at hx ⊢
    exact hx

/-- The first m−1 selecting idempotents act as identity; the next acts as zero. -/
theorem testModule_idempotent_action (m : ℕ) [NeZero m] (i : Fin m) (x : TestModule m) :
    selectionIdempotent i.val • x = if i = lastIndex m then 0 else x := by
  classical
  unfold selectionIdempotent
  rw [smul_assoc,add_smul,one_smul,testModule_basis_action]
  split_ifs
  · rw [show (-1 : ℂ) • x = -x from neg_one_smul ℂ x,add_neg_cancel,smul_zero]
  · rw [one_smul,← two_smul ℂ x,smul_smul]
    norm_num
end LittleFinitistic

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Selection_SelectionIteration
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideModule _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.DirectedBound.DirectedSystem.cover_addCommGroup _root_.OAI.LittleFinitistic.FiniteSelectionFamily.ringModule _root_.OAI.LittleFinitistic.FiniteSelectionFamily.tower _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.SelectedBaseIterates.input_finite _root_.OAI.LittleFinitistic.SelectedBaseIterates.input_finiteD _root_.OAI.LittleFinitistic.SelectedFirstBlockFamily.derivedInflation_additive _root_.OAI.LittleFinitistic.SelectedFirstBlockFamily.inflation_preservesFiniteColimits _root_.OAI.LittleFinitistic.SelectedFirstBlockFamily.inflation_preservesFiniteLimits _root_.OAI.LittleFinitistic.SelectedNativeEvaluation.instFiniteDimensionalComplexCarrierH _root_.OAI.LittleFinitistic.SelectedOrdinaryAlgebra.D_finite _root_.OAI.LittleFinitistic.SelectedOrdinaryAlgebra.base_finite _root_.OAI.LittleFinitistic.SelectedOrdinaryAlgebra.term_finite _root_.OAI.LittleFinitistic.SelectedOrdinaryAlgebra.term_projective _root_.OAI.LittleFinitistic.SelectedOrdinaryModules.instFiniteAInflated _root_.OAI.LittleFinitistic.SelectedOrdinaryModules.instIsScalarTowerComplexAInflated _root_.OAI.LittleFinitistic.SelectedOrdinaryModules.instIsScalarTowerComplexBPInflated _root_.OAI.LittleFinitistic.SelectedOrdinaryModules.instIsScalarTowerComplexDInflated _root_.OAI.LittleFinitistic.SelectedOrdinaryModules.instModuleAInflated _root_.OAI.LittleFinitistic.SelectedOrdinaryModules.instModuleBComplexPInflated _root_.OAI.LittleFinitistic.SelectedOrdinaryModules.instModuleDInflated _root_.OAI.LittleFinitistic.SelectedPDDetection.residueModuleK _root_.OAI.LittleFinitistic.SelectedTensor.comparison_isIso _root_.OAI.LittleFinitistic.SelectionEncoding.instRingDirectedAlgebra _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
attribute [-simp] _root_.OAI.ExternalTensor.Section4.sum_hom _root_.OAI.LittleFinitistic.FinitePresentation.fromModel_T _root_.OAI.LittleFinitistic.FinitePresentation.fromModel_u _root_.OAI.LittleFinitistic.FinitePresentation.fromModel_v _root_.OAI.LittleFinitistic.FinitePresentation.fromModel_w _root_.OAI.LittleFinitistic.FinitePresentation.toModel_T _root_.OAI.LittleFinitistic.FinitePresentation.toModel_U _root_.OAI.LittleFinitistic.FinitePresentation.toModel_V _root_.OAI.LittleFinitistic.FinitePresentation.toModel_W
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
namespace LittleFinitistic
open CategoryTheory

theorem identityAt_step (M : ModuleCat SelectionRing) (q : ℕ)
    (h : IdentityAt M (q+1)) : IdentityAt (selectionStep M) q := by
  intro x
  apply Subtype.ext
  change selectionAutomorphism 1 (selectionIdempotent q) • x.val = x.val
  rw [selectionAutomorphism_idempotent]
  exact_mod_cast h x.val

theorem zeroAt_step (M : ModuleCat SelectionRing) (q : ℕ)
    (h : ZeroAt M (q+1)) : ZeroAt (selectionStep M) q := by
  intro x
  apply Subtype.ext
  change selectionAutomorphism 1 (selectionIdempotent q) • x.val = 0
  rw [selectionAutomorphism_idempotent]
  exact_mod_cast h x.val

theorem selectionStep_nontrivial (M : ModuleCat SelectionRing) [Nontrivial M]
    (h : IdentityAt M 0) : Nontrivial (selectionStep M) := by
  obtain ⟨x,y,hxy⟩ := exists_pair_ne M
  exact ⟨⟨⟨x,h x⟩,⟨y,h y⟩,fun he => hxy (congrArg Subtype.val he)⟩⟩

theorem selectionStep_subsingleton (M : ModuleCat SelectionRing)
    (h : ZeroAt M 0) : Subsingleton (selectionStep M) := by
  refine ⟨fun x y => Subtype.ext ?_⟩
  have hx : x.val = 0 := (x.property).symm.trans (h x.val)
  have hy : y.val = 0 := (y.property).symm.trans (h y.val)
  exact hx.trans hy.symm

theorem identityAt_iterate (M : ModuleCat SelectionRing) (n q : ℕ)
    (h : IdentityAt M (q+n)) : IdentityAt (selectionIterate M n) q := by
  induction n generalizing q with
  | zero => simpa [selectionIterate] using h
  | succ n ih =>
    apply identityAt_step
    apply ih
    simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h

theorem zeroAt_iterate (M : ModuleCat SelectionRing) (n q : ℕ)
    (h : ZeroAt M (q+n)) : ZeroAt (selectionIterate M n) q := by
  induction n generalizing q with
  | zero => simpa [selectionIterate] using h
  | succ n ih =>
    apply zeroAt_step
    apply ih
    simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h

theorem testObject_identityAt (m : ℕ) [NeZero m] (q : ℕ) (hq : q < m-1) :
    IdentityAt (testObject m) q := by
  intro x
  let i : Fin m := ⟨q,by omega⟩
  have hi : i ≠ lastIndex m := by
    intro h
    have hv := congrArg Fin.val h
    change q = m-1 at hv
    omega
  exact (testModule_idempotent_action m i x).trans (ite_eq_right hi)

theorem testObject_zeroAt (m : ℕ) [NeZero m] : ZeroAt (testObject m) (m-1) := by
  intro x
  exact (testModule_idempotent_action m (lastIndex m) x).trans (ite_eq_left rfl)

theorem selectionIterate_test_nontrivial (m : ℕ) [NeZero m] (n : ℕ) (hn : n < m) :
    Nontrivial (selectionIterate (testObject m) n) := by
  induction n with
  | zero => exact testModule_nontrivial m
  | succ n ih =>
    have := ih (by omega)
    apply selectionStep_nontrivial
    apply identityAt_iterate
    simpa only [Nat.zero_add] using testObject_identityAt m n (by omega)

theorem selectionIterate_test_subsingleton (m : ℕ) [NeZero m] :
    Subsingleton (selectionIterate (testObject m) m) := by
  have hm : m = (m-1)+1 := by have := NeZero.ne m; omega
  have hzero : ZeroAt (selectionIterate (testObject m) (m-1)) 0 :=
    zeroAt_iterate (testObject m) (m-1) 0 (by simpa using testObject_zeroAt m)
  have h := selectionStep_subsingleton _ hzero
  change Subsingleton (selectionIterate (testObject m) ((m-1)+1)) at h
  rwa [← hm] at h

end LittleFinitistic

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Selected_SelectedOrdinaryAlgebra
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.term_finiteDimensional _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.leftModule _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FiniteSelectionFamily.instFiniteDimensionalComplexCarrierVector _root_.OAI.LittleFinitistic.FiniteSelectionFamily.ringModule _root_.OAI.LittleFinitistic.FiniteSelectionFamily.tower _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.OrdinarySimulation.BimoduleO.commuteRightTensor _root_.OAI.LittleFinitistic.OrdinarySimulation.TensorResolution.augmentation_epi _root_.OAI.LittleFinitistic.OrdinarySimulation.TensorResolution.integerBimoduleRight_projective _root_.OAI.LittleFinitistic.OrdinarySimulation.TensorResolution.integerTerm_moduleProjective _root_.OAI.LittleFinitistic.OrdinarySimulation.TensorResolution.projectiveTerm _root_.OAI.LittleFinitistic.OrdinarySimulation.TensorResolution.term_projective _root_.OAI.LittleFinitistic.OrdinarySimulation.TerminalSimple.instModuleMulOppositeChainAlgebra _root_.OAI.LittleFinitistic.OrdinarySimulation.TerminalSimple.tower _root_.OAI.LittleFinitistic.OrdinarySimulation.XResolution.rightTerm_projective _root_.OAI.LittleFinitistic.PDBarQuotient.leftModule _root_.OAI.LittleFinitistic.SelectedBaseIterates.input_finite _root_.OAI.LittleFinitistic.SelectedBaseIterates.input_finiteD _root_.OAI.LittleFinitistic.SelectedFirstBlockFamily.derivedInflation_additive _root_.OAI.LittleFinitistic.SelectedFirstBlockFamily.inflation_preservesFiniteColimits _root_.OAI.LittleFinitistic.SelectedFirstBlockFamily.inflation_preservesFiniteLimits _root_.OAI.LittleFinitistic.SelectedOrdinaryModules.instFiniteAInflated _root_.OAI.LittleFinitistic.SelectedOrdinaryModules.instIsScalarTowerComplexAInflated _root_.OAI.LittleFinitistic.SelectedOrdinaryModules.instIsScalarTowerComplexBPInflated _root_.OAI.LittleFinitistic.SelectedOrdinaryModules.instIsScalarTowerComplexDInflated _root_.OAI.LittleFinitistic.SelectedOrdinaryModules.instModuleAInflated _root_.OAI.LittleFinitistic.SelectedOrdinaryModules.instModuleBComplexPInflated _root_.OAI.LittleFinitistic.SelectedOrdinaryModules.instModuleDInflated _root_.OAI.LittleFinitistic.SelectedPDDetection.residueModuleK _root_.OAI.LittleFinitistic.SelectedTensor.comparison_isIso
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace LittleFinitistic.SelectedOrdinaryAlgebra
open SelectedFixedDiagram QuadraticEncoding
open OrdinarySimulation

instance X_finite : FiniteDimensional ℂ X := ordinary_finite _ _ _

instance A_finite : FiniteDimensional ℂ A :=
  inferInstanceAs (FiniteDimensional ℂ (D × X))
end LittleFinitistic.SelectedOrdinaryAlgebra

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Selection_FiniteSelectionFamily
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideModule _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.PDBarQuotient.leftModule _root_.OAI.LittleFinitistic.SelectedBaseIterates.input_finite _root_.OAI.LittleFinitistic.SelectedBaseIterates.input_finiteD _root_.OAI.LittleFinitistic.SelectedFirstBlockFamily.derivedInflation_additive _root_.OAI.LittleFinitistic.SelectedFirstBlockFamily.inflation_preservesFiniteColimits _root_.OAI.LittleFinitistic.SelectedFirstBlockFamily.inflation_preservesFiniteLimits _root_.OAI.LittleFinitistic.SelectedOrdinaryAlgebra.A_finite _root_.OAI.LittleFinitistic.SelectedOrdinaryAlgebra.D_finite _root_.OAI.LittleFinitistic.SelectedOrdinaryAlgebra.X_finite _root_.OAI.LittleFinitistic.SelectedOrdinaryAlgebra.base_finite _root_.OAI.LittleFinitistic.SelectedOrdinaryAlgebra.term_finite _root_.OAI.LittleFinitistic.SelectedOrdinaryAlgebra.term_projective _root_.OAI.LittleFinitistic.SelectedOrdinaryModules.instAddCommGroupInflated _root_.OAI.LittleFinitistic.SelectedOrdinaryModules.instFiniteAInflated _root_.OAI.LittleFinitistic.SelectedOrdinaryModules.instFiniteDimensionalComplexInflated _root_.OAI.LittleFinitistic.SelectedOrdinaryModules.instIsScalarTowerComplexAInflated _root_.OAI.LittleFinitistic.SelectedOrdinaryModules.instIsScalarTowerComplexBPInflated _root_.OAI.LittleFinitistic.SelectedOrdinaryModules.instIsScalarTowerComplexDInflated _root_.OAI.LittleFinitistic.SelectedOrdinaryModules.instModuleAInflated _root_.OAI.LittleFinitistic.SelectedOrdinaryModules.instModuleBComplexPInflated _root_.OAI.LittleFinitistic.SelectedOrdinaryModules.instModuleComplexInflated _root_.OAI.LittleFinitistic.SelectedOrdinaryModules.instModuleDInflated _root_.OAI.LittleFinitistic.SelectedPDDetection.residueModuleK
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits
attribute [local instance] HasDerivedCategory.standard HasExt.standard
namespace LittleFinitistic.FiniteSelectionFamily
open SelectedFixedDiagram QuadraticEncoding

/-- Evaluation on three copies preserves and reflects the zero module. -/
theorem module_zero (Y : S) : IsZero (module Y) ↔ Subsingleton Y.val := by
  constructor
  · intro h
    let := ModuleCat.subsingleton_of_isZero h
    have inj : Function.Injective ((representation Y).inclusion 0) := by
      intro x y hxy
      have := congrArg ((representation Y).projection 0) hxy
      simpa only [Representation.projection_inclusion] using this
    exact inj.subsingleton
  · intro h
    let := h
    have : Subsingleton (representation Y).Evaluation :=
      inferInstanceAs (Subsingleton (Y.val × Y.val × Y.val))
    exact ModuleCat.isZero_of_subsingleton _

/-- The same exact zero criterion after embedding in the actual derived category. -/
theorem derived_zero (Y : S) : IsZero (derived Y) ↔ Subsingleton Y.val := by
  rw [← module_zero Y]
  constructor
  · intro h
    exact ((DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat (B P)) 0).app
      (module Y)).isZero_iff.mp ((DerivedCategory.homologyFunctor (ModuleCat (B P)) 0).map_isZero h)
  · exact (DerivedCategory.singleFunctor (ModuleCat (B P)) 0).map_isZero

/-- Iteration is literally the Section 2 selection operation. -/
theorem iterate_val (j : ℕ) (Y : S) : ((H^[j]) Y).val = selectionIterate Y.val j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [Function.iterate_succ_apply']
    change selectionStep ((H^[j]) Y).val = selectionStep (selectionIterate Y.val j)
    exact congrArg selectionStep ih

end LittleFinitistic.FiniteSelectionFamily

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Selected_SelectedBaseIterates
attribute [-instance] _root_.OAI.LittleFinitistic.BimoduleTotal.augmentationComparisonOnChains_isIso _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.OrdinarySimulation.BimoduleO.commuteRightTensor _root_.OAI.LittleFinitistic.OrdinarySimulation.TensorResolution.augmentation_epi _root_.OAI.LittleFinitistic.OrdinarySimulation.TensorResolution.integerBimoduleRight_projective _root_.OAI.LittleFinitistic.OrdinarySimulation.TensorResolution.integerTerm_moduleProjective _root_.OAI.LittleFinitistic.OrdinarySimulation.TensorResolution.projectiveTerm _root_.OAI.LittleFinitistic.OrdinarySimulation.TensorResolution.term_projective _root_.OAI.LittleFinitistic.OrdinarySimulation.TerminalSimple.instModuleMulOppositeChainAlgebra _root_.OAI.LittleFinitistic.OrdinarySimulation.TerminalSimple.tower _root_.OAI.LittleFinitistic.OrdinarySimulation.XResolution.rightTerm_projective _root_.OAI.LittleFinitistic.PDBarQuotient.leftModule _root_.OAI.LittleFinitistic.SelectedFirstBlockFamily.derivedInflation_additive _root_.OAI.LittleFinitistic.SelectedFirstBlockFamily.inflation_preservesFiniteColimits _root_.OAI.LittleFinitistic.SelectedFirstBlockFamily.inflation_preservesFiniteLimits _root_.OAI.LittleFinitistic.SelectedPDDetection.residueModuleK
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace LittleFinitistic.SelectedBaseIterates
open SelectedOrdinaryAlgebra SelectedOrdinaryModules

local instance instModuleComplexCarrierD_r8d7edd_1 (N : ModuleCat.{0} D) : Module ℂ N := DerivedBar.BimoduleTensor.scalarModule ℂ D N
local instance instIsScalarTowerComplexDCarrier_r8d7edd_1 (N : ModuleCat.{0} D) : IsScalarTower ℂ D N where
  smul_assoc c d n := by
    change (c • d) • n = (algebraMap ℂ D c) • (d • n)
    have hd : c • d = (algebraMap ℂ D c) * d := by
      exact Algebra.smul_def c d
    rw [hd, mul_smul]
local instance instHasDerivedCategoryModuleCatD_r8d7edd_1 : HasDerivedCategory.{1} (ModuleCat.{0} D) :=
  HasDerivedCategory.standard (ModuleCat.{0} D)
/-- A global-dimension bound on D bounds the amplitude of every derived iterate. -/
theorem bounded (g : ℕ) (hg : ∀ M : ModuleCat.{0} D, HasProjectiveDimensionLE M g)
    (Y : FiniteSelectionFamily.S.{0}) (r : ℕ) :
    (object Y r).IsGE (-((r*(g+2) : ℕ) : ℤ)) ∧ (object Y r).IsLE 0 :=
  DerivedBar.IterateSupport.bounded_amplitude ℂ D X g hg (input Y) r
end LittleFinitistic.SelectedBaseIterates

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Selected_SelectedShiftedRealization
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideModule _root_.OAI.LittleFinitistic.PDBarQuotient.leftModule _root_.OAI.LittleFinitistic.SelectedBaseIterates.input_finite _root_.OAI.LittleFinitistic.SelectedBaseIterates.input_finiteD _root_.OAI.LittleFinitistic.SelectedFirstBlockFamily.derivedInflation_additive _root_.OAI.LittleFinitistic.SelectedFirstBlockFamily.inflation_preservesFiniteColimits _root_.OAI.LittleFinitistic.SelectedFirstBlockFamily.inflation_preservesFiniteLimits _root_.OAI.LittleFinitistic.SelectedOrdinaryModules.instAddCommGroupInflated _root_.OAI.LittleFinitistic.SelectedOrdinaryModules.instFiniteAInflated _root_.OAI.LittleFinitistic.SelectedOrdinaryModules.instFiniteDimensionalComplexInflated _root_.OAI.LittleFinitistic.SelectedOrdinaryModules.instIsScalarTowerComplexAInflated _root_.OAI.LittleFinitistic.SelectedOrdinaryModules.instIsScalarTowerComplexBPInflated _root_.OAI.LittleFinitistic.SelectedOrdinaryModules.instIsScalarTowerComplexDInflated _root_.OAI.LittleFinitistic.SelectedOrdinaryModules.instModuleAInflated _root_.OAI.LittleFinitistic.SelectedOrdinaryModules.instModuleBComplexPInflated _root_.OAI.LittleFinitistic.SelectedOrdinaryModules.instModuleComplexInflated _root_.OAI.LittleFinitistic.SelectedOrdinaryModules.instModuleDInflated _root_.OAI.LittleFinitistic.SelectedPDDetection.residueModuleK
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits
attribute [local instance] HasDerivedCategory.standard HasExt.standard
namespace LittleFinitistic.SelectedShiftedRealization
open SelectedFixedDiagram QuadraticEncoding SelectedOrdinaryAlgebra
attribute [local instance] preservesBinaryBiproducts_of_preservesBiproducts

theorem isZero_iff (j : ℕ) (Y : FiniteSelectionFamily.S.{0}) :
    IsZero ((G.obj^[j]) (FiniteSelectionFamily.derived Y)) ↔
      Subsingleton (selectionIterate Y.val j) :=
  (ExternalTensor.Binomial.iteration_isZero_iff G FiniteSelectionFamily.derived
    FiniteSelectionFamily.H b 3 realization j Y).trans
    ((FiniteSelectionFamily.derived_zero _).trans
      (by rw [FiniteSelectionFamily.iterate_val]))

end LittleFinitistic.SelectedShiftedRealization

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Selected_SelectedOrdinaryOrbit
attribute [-instance] _root_.OAI.LittleFinitistic.PDBarQuotient.leftModule _root_.OAI.LittleFinitistic.SelectedPDDetection.residueModuleK
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
namespace LittleFinitistic.SelectedOrdinaryOrbit
open SelectedOrdinaryAlgebra SelectedFixedDiagram QuadraticEncoding

attribute [local instance] OAI.LittleFinitistic.SelectedOrdinaryOrbit.instHasDerivedCategoryModuleCatD
attribute [local instance] OAI.LittleFinitistic.SelectedOrdinaryOrbit.instHasDerivedCategoryModuleCatBComplexP
attribute [local instance] OAI.LittleFinitistic.SelectedOrdinaryOrbit.resolution_projective
/-- Every even original-X iterate is zero exactly at the original selection stopping time. -/
theorem isZero_iff (Y : FiniteSelectionFamily.S.{0}) (j : ℕ) :
    IsZero (SelectedBaseIterates.object Y (2*j)) ↔ Subsingleton (selectionIterate Y.val j) :=
  (evenIteration Y j).isZero_iff.trans
    ((BlockModule.derivedFirst_isZero_iff (B P)
      ((B P) ⊗[ℂ] OrdinarySimulation.ChainAlgebra ℂ length) _).trans
        (SelectedShiftedRealization.isZero_iff j Y))

/-- Actual extinction/survival pair required by the main theorem, on one fixed A. -/
theorem extinction (m : ℕ) [NeZero m] :
    IsZero (SelectedBaseIterates.object (FiniteSelectionFamily.test m) (2*m)) ∧
      ¬ IsZero (SelectedBaseIterates.object (FiniteSelectionFamily.test m) (2*m-2)) := by
  constructor
  · exact (isZero_iff (FiniteSelectionFamily.test m) m).mpr (selectionIterate_test_subsingleton m)
  · have hm := NeZero.pos m
    have he : 2*m-2 = 2*(m-1) := by omega
    rw [he]
    intro hz
    exact @not_subsingleton _ (selectionIterate_test_nontrivial m (m-1) (by omega))
      ((isZero_iff (FiniteSelectionFamily.test m) (m-1)).mp hz)
end LittleFinitistic.SelectedOrdinaryOrbit

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Ordinary_OrdinaryTensorGlobalDimension
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.OrdinarySimulation.BimoduleO.commuteChainLeft _root_.OAI.LittleFinitistic.OrdinarySimulation.BimoduleO.commuteChainRight _root_.OAI.LittleFinitistic.OrdinarySimulation.BimoduleO.commuteRightTensor _root_.OAI.LittleFinitistic.OrdinarySimulation.BimoduleO.commuteTensorRight _root_.OAI.LittleFinitistic.OrdinarySimulation.BimoduleO.instIsScalarTowerChainAlgebra _root_.OAI.LittleFinitistic.OrdinarySimulation.BimoduleO.instModuleChainAlgebra _root_.OAI.LittleFinitistic.OrdinarySimulation.BimoduleO.instSMulCommClassChainAlgebraEnveloping _root_.OAI.LittleFinitistic.OrdinarySimulation.BimoduleO.leftModule _root_.OAI.LittleFinitistic.OrdinarySimulation.BimoduleO.towerTensor _root_.OAI.LittleFinitistic.OrdinarySimulation.Compression.instIsScalarTowerChainAlgebra _root_.OAI.LittleFinitistic.OrdinarySimulation.Compression.instModuleChainAlgebra _root_.OAI.LittleFinitistic.OrdinarySimulation.Compression.instSMulCommClassChainAlgebra _root_.OAI.LittleFinitistic.OrdinarySimulation.TensorResolution.augmentation_epi _root_.OAI.LittleFinitistic.OrdinarySimulation.TensorResolution.integerBimoduleRight_projective _root_.OAI.LittleFinitistic.OrdinarySimulation.TensorResolution.integerTerm_moduleProjective _root_.OAI.LittleFinitistic.OrdinarySimulation.TensorResolution.projectiveTerm _root_.OAI.LittleFinitistic.OrdinarySimulation.TensorResolution.term_projective _root_.OAI.LittleFinitistic.OrdinarySimulation.TerminalSimple.instModuleMulOppositeChainAlgebra _root_.OAI.LittleFinitistic.OrdinarySimulation.TerminalSimple.tower _root_.OAI.LittleFinitistic.OrdinarySimulation.TerminalTensor.commuteActions _root_.OAI.LittleFinitistic.OrdinarySimulation.TerminalTensor.instModuleMulOppositeTensorProductChainAlgebra _root_.OAI.LittleFinitistic.OrdinarySimulation.TerminalTensor.towerRight _root_.OAI.LittleFinitistic.OrdinarySimulation.XResolution.rightTerm_projective _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.SelectedBaseIterates.input_finite _root_.OAI.LittleFinitistic.SelectedBaseIterates.input_finiteD _root_.OAI.LittleFinitistic.SelectedFirstBlockFamily.derivedInflation_additive _root_.OAI.LittleFinitistic.SelectedFirstBlockFamily.inflation_preservesFiniteColimits _root_.OAI.LittleFinitistic.SelectedFirstBlockFamily.inflation_preservesFiniteLimits _root_.OAI.LittleFinitistic.SelectedOrdinaryAlgebra.A_finite _root_.OAI.LittleFinitistic.SelectedOrdinaryAlgebra.D_finite _root_.OAI.LittleFinitistic.SelectedOrdinaryModules.instFiniteAInflated _root_.OAI.LittleFinitistic.SelectedOrdinaryModules.instIsScalarTowerComplexAInflated _root_.OAI.LittleFinitistic.SelectedOrdinaryModules.instIsScalarTowerComplexDInflated _root_.OAI.LittleFinitistic.SelectedOrdinaryModules.instModuleAInflated _root_.OAI.LittleFinitistic.SelectedOrdinaryModules.instModuleDInflated _root_.OAI.LittleFinitistic.SelectedPDDetection.residueModuleK _root_.OAI.LittleFinitistic.SelectionEncoding.instRingDirectedAlgebra _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory
open scoped TensorProduct
namespace LittleFinitistic.OrdinarySimulation
universe u v
variable {k B : Type u} [Field k] [Ring B] [Algebra k B]

/-- The corresponding bound holds for each arbitrary left or right module. -/
theorem tensor_projectiveDimension_bound (DB : DirectedBound.DirectedSystem k B 3) (l : ℕ) :
    (∀ M : ModuleCat.{max u v} (B ⊗[k] ChainAlgebra k l), projectiveDimension M ≤ (3*l+2 : ℕ)) ∧
    (∀ M : ModuleCat.{max u v} (B ⊗[k] ChainAlgebra k l)ᵐᵒᵖ, projectiveDimension M ≤ (3*l+2 : ℕ)) := by
  have h := DirectedBound.DirectedSystem.both_sides_projectiveDimension_le.{u,v}
    (TensorDirected.directedSystem DB (ChainAlgebra.directedSystem k l))
  have hn : (l+1)*3-1 = 3*l+2 := by omega
  simpa only [hn] using h

end LittleFinitistic.OrdinarySimulation

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Ordinary_OrdinaryGlobalDimension
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.ConcreteTensorEvaluation.vertexScalarTower _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.OrdinarySimulation.BimoduleO.commuteChainLeft _root_.OAI.LittleFinitistic.OrdinarySimulation.BimoduleO.commuteChainRight _root_.OAI.LittleFinitistic.OrdinarySimulation.BimoduleO.commuteRightTensor _root_.OAI.LittleFinitistic.OrdinarySimulation.BimoduleO.commuteTensorRight _root_.OAI.LittleFinitistic.OrdinarySimulation.BimoduleO.instIsScalarTowerChainAlgebra _root_.OAI.LittleFinitistic.OrdinarySimulation.BimoduleO.instModuleChainAlgebra _root_.OAI.LittleFinitistic.OrdinarySimulation.BimoduleO.instSMulCommClassChainAlgebraEnveloping _root_.OAI.LittleFinitistic.OrdinarySimulation.BimoduleO.leftModule _root_.OAI.LittleFinitistic.OrdinarySimulation.BimoduleO.towerTensor _root_.OAI.LittleFinitistic.OrdinarySimulation.Compression.instIsScalarTowerChainAlgebra _root_.OAI.LittleFinitistic.OrdinarySimulation.Compression.instModuleChainAlgebra _root_.OAI.LittleFinitistic.OrdinarySimulation.Compression.instSMulCommClassChainAlgebra _root_.OAI.LittleFinitistic.OrdinarySimulation.TensorResolution.augmentation_epi _root_.OAI.LittleFinitistic.OrdinarySimulation.TensorResolution.integerBimoduleRight_projective _root_.OAI.LittleFinitistic.OrdinarySimulation.TensorResolution.integerTerm_moduleProjective _root_.OAI.LittleFinitistic.OrdinarySimulation.TensorResolution.projectiveTerm _root_.OAI.LittleFinitistic.OrdinarySimulation.TensorResolution.term_projective _root_.OAI.LittleFinitistic.OrdinarySimulation.TerminalSimple.instModuleMulOppositeChainAlgebra _root_.OAI.LittleFinitistic.OrdinarySimulation.TerminalSimple.tower _root_.OAI.LittleFinitistic.OrdinarySimulation.TerminalTensor.commuteActions _root_.OAI.LittleFinitistic.OrdinarySimulation.TerminalTensor.instModuleMulOppositeTensorProductChainAlgebra _root_.OAI.LittleFinitistic.OrdinarySimulation.TerminalTensor.towerRight _root_.OAI.LittleFinitistic.OrdinarySimulation.XResolution.rightTerm_projective _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.evaluationModule _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.instIsScalarTowerBEvaluation _root_.OAI.LittleFinitistic.QuadraticEncoding.Representation.instSMulCommClassBEvaluation _root_.OAI.LittleFinitistic.QuadraticEncoding.boundedEvaluationAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.boundedEvaluationLinear _root_.OAI.LittleFinitistic.QuadraticEncoding.boundedEvaluationShift _root_.OAI.LittleFinitistic.QuadraticEncoding.boundedEvaluationTriangulated _root_.OAI.LittleFinitistic.QuadraticEncoding.boundedKLinear _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.degreeZeroAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.degreeZeroLinear _root_.OAI.LittleFinitistic.QuadraticEncoding.finiteEvaluationAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.finiteEvaluationShift _root_.OAI.LittleFinitistic.QuadraticEncoding.finiteEvaluationTriangulated _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.vertexModuleFinite _root_.OAI.LittleFinitistic.QuadraticEncoding.vertexModuleProjective _root_.OAI.LittleFinitistic.SelectedBaseIterates.input_finite _root_.OAI.LittleFinitistic.SelectedBaseIterates.input_finiteD _root_.OAI.LittleFinitistic.SelectedFirstBlockFamily.derivedInflation_additive _root_.OAI.LittleFinitistic.SelectedFirstBlockFamily.inflation_preservesFiniteColimits _root_.OAI.LittleFinitistic.SelectedFirstBlockFamily.inflation_preservesFiniteLimits _root_.OAI.LittleFinitistic.SelectedOrdinaryAlgebra.A_finite _root_.OAI.LittleFinitistic.SelectedOrdinaryAlgebra.D_finite _root_.OAI.LittleFinitistic.SelectedOrdinaryAlgebra.X_finite _root_.OAI.LittleFinitistic.SelectedOrdinaryAlgebra.term_finite _root_.OAI.LittleFinitistic.SelectedOrdinaryAlgebra.term_projective _root_.OAI.LittleFinitistic.SelectedOrdinaryModules.instFiniteAInflated _root_.OAI.LittleFinitistic.SelectedOrdinaryModules.instIsScalarTowerComplexAInflated _root_.OAI.LittleFinitistic.SelectedOrdinaryModules.instIsScalarTowerComplexDInflated _root_.OAI.LittleFinitistic.SelectedOrdinaryModules.instModuleAInflated _root_.OAI.LittleFinitistic.SelectedOrdinaryModules.instModuleDInflated _root_.OAI.LittleFinitistic.SelectedPDDetection.residueModuleK _root_.OAI.LittleFinitistic.SelectedTensor.comparison_isIso _root_.OAI.LittleFinitistic.SelectionEncoding.instRingDirectedAlgebra _root_.OAI.LittleFinitistic.SourceEvaluation.finite_first _root_.OAI.LittleFinitistic.SourceEvaluation.finite_second _root_.OAI.LittleFinitistic.SourceEvaluation.first_inverted _root_.OAI.LittleFinitistic.SourceEvaluation.instAdditiveKFiniteVectorHomotopyFinite _root_.OAI.LittleFinitistic.SourceEvaluation.instAdditiveKHomotopyCategoryIntModuleCatUpEvaluation _root_.OAI.LittleFinitistic.SourceEvaluation.instAdditiveQFiniteVectorDerivedDerived _root_.OAI.LittleFinitistic.SourceEvaluation.instAdditiveQFiniteVectorHomotopyQuotientFinite _root_.OAI.LittleFinitistic.SourceEvaluation.instAdditiveQHomotopyCategoryIntModuleCatUpQuotientHomotopy _root_.OAI.LittleFinitistic.SourceEvaluation.instCommShiftKFiniteVectorHomotopyFiniteInt _root_.OAI.LittleFinitistic.SourceEvaluation.instCommShiftKHomotopyCategoryIntModuleCatUpEvaluation _root_.OAI.LittleFinitistic.SourceEvaluation.instCommShiftQFiniteVectorDerivedDerivedInt _root_.OAI.LittleFinitistic.SourceEvaluation.instCommShiftQFiniteVectorHomotopyQuotientFiniteInt _root_.OAI.LittleFinitistic.SourceEvaluation.instIsTriangulatedKFiniteVectorHomotopyFinite _root_.OAI.LittleFinitistic.SourceEvaluation.instIsTriangulatedKHomotopyCategoryIntModuleCatUpEvaluation _root_.OAI.LittleFinitistic.SourceEvaluation.instIsTriangulatedQFiniteVectorDerivedDerived _root_.OAI.LittleFinitistic.SourceEvaluation.instIsTriangulatedQFiniteVectorHomotopyQuotientFinite _root_.OAI.LittleFinitistic.SourceEvaluation.instLiftingKQHomotopyCategoryIntModuleCatUpQSigmaEvaluationQuotientHomotopy _root_.OAI.LittleFinitistic.SourceEvaluation.instLinearKHomotopyCategoryIntModuleCatUpEvaluation _root_.OAI.LittleFinitistic.SourceEvaluation.instLinearQHomotopyCategoryIntModuleCatUpQuotientHomotopy _root_.OAI.LittleFinitistic.SourceEvaluation.second_inverted _root_.OAI.LittleFinitistic.SourceImageEvaluation.instAdditiveKaroubiQRelationsFiniteVectorDerivedCompleted _root_.OAI.LittleFinitistic.SourceModelBridge.instAdditiveKBoundedKToBounded _root_.OAI.LittleFinitistic.SourceModelBridge.instCommShiftKBoundedKToBoundedInt _root_.OAI.LittleFinitistic.SourceModelBridge.instIsTriangulatedKBoundedKToBounded _root_.OAI.LittleFinitistic.SourceModelBridge.instLinearKBoundedKToBounded _root_.OAI.LittleFinitistic.SourceQuotientAction.instIsIsoQA01OfNatFinHAddNat _root_.OAI.LittleFinitistic.SourceQuotientAction.instIsIsoQA12OfNatFinHAddNat _root_.OAI.LittleFinitistic.SourceQuotientAction.singleAdditive _root_.OAI.LittleFinitistic.SourceQuotientAction.singleLinear _root_.OAI.LittleFinitistic.SourceQuotientAction.stalkAdditive _root_.OAI.LittleFinitistic.SourceQuotientAction.stalkLinear _root_.OAI.LittleFinitistic.SourceVerdier.linearK _root_.OAI.LittleFinitistic.SourceVerdier.linearProj _root_.OAI.LittleFinitistic.SourceVerdier.linearQ _root_.OAI.LittleFinitistic.SourceVerdier.linearQuotient _root_.OAI.LittleFinitistic.SourceVerdier.s'_inverted _root_.OAI.LittleFinitistic.SourceVerdier.s_inverted _root_.OAI.LittleFinitistic.SourceVerdier.shiftLinearK _root_.OAI.LittleFinitistic.SourceVerdier.shiftLinearQ _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory
open scoped TensorProduct
namespace LittleFinitistic.OrdinarySimulation
universe u v
variable {k B : Type u} [Field k] [Ring B] [Algebra k B]

/-- The manuscript's exact bound for D, on both sides and for arbitrary modules. -/
theorem ordinary_globalDimension_bound (DB : DirectedBound.DirectedSystem k B 3) (l : ℕ) :
    (⨆ M : ModuleCat.{max u v} (AlgebraD k l B), projectiveDimension M) ≤ (3*l+2 : ℕ) ∧
    (⨆ M : ModuleCat.{max u v} (AlgebraD k l B)ᵐᵒᵖ, projectiveDimension M) ≤ (3*l+2 : ℕ) := by
  have hB := DirectedBound.DirectedSystem.both_sides_projectiveDimension_le.{u,v} DB
  have hBC := tensor_projectiveDimension_bound.{u,v} DB l
  have hL (M : ModuleCat.{max u v} B) : projectiveDimension M ≤ (3*l+2 : ℕ) := by
    apply (hB.1 M).trans
    exact_mod_cast (show 3-1 ≤ 3*l+2 by omega)
  have hR (M : ModuleCat.{max u v} Bᵐᵒᵖ) : projectiveDimension M ≤ (3*l+2 : ℕ) := by
    apply (hB.2 M).trans
    exact_mod_cast (show 3-1 ≤ 3*l+2 by omega)
  exact ⟨iSup_le (fun M => ProductModules.product_module_bound B (B ⊗[k] ChainAlgebra k l)
      (3*l+2) hL hBC.1 M),
    iSup_le (fun M => ProductModules.opposite_product_module_bound B (B ⊗[k] ChainAlgebra k l)
      (3*l+2) hR hBC.2 M)⟩

variable {V W U : Type u} [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
  [AddCommGroup U] [Module k U]

/-- The bound for the actual three-vertex coefficient algebra and the actual Section 5 product D. -/
theorem source_ordinary_globalDimension_bound (μ : W →ₗ[k] V →ₗ[k] U) (l : ℕ) :
    (⨆ M : ModuleCat.{max u v} (AlgebraD k l (ThreeVertexAlgebra μ)), projectiveDimension M) ≤ (3*l+2 : ℕ) ∧
    (⨆ M : ModuleCat.{max u v} (AlgebraD k l (ThreeVertexAlgebra μ))ᵐᵒᵖ, projectiveDimension M) ≤ (3*l+2 : ℕ) :=
  ordinary_globalDimension_bound (ThreeVertexAlgebra.directedSystem μ) l
end LittleFinitistic.OrdinarySimulation

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Selected_SelectedOrdinaryDimension
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.leftModule _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FiniteSelectionFamily.ringModule _root_.OAI.LittleFinitistic.FiniteSelectionFamily.tower _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.OrdinarySimulation.BimoduleO.commuteRightTensor _root_.OAI.LittleFinitistic.OrdinarySimulation.TensorResolution.augmentation_epi _root_.OAI.LittleFinitistic.OrdinarySimulation.TensorResolution.integerBimoduleRight_projective _root_.OAI.LittleFinitistic.OrdinarySimulation.TensorResolution.integerTerm_moduleProjective _root_.OAI.LittleFinitistic.OrdinarySimulation.TensorResolution.projectiveTerm _root_.OAI.LittleFinitistic.OrdinarySimulation.TensorResolution.term_projective _root_.OAI.LittleFinitistic.OrdinarySimulation.TerminalSimple.instModuleMulOppositeChainAlgebra _root_.OAI.LittleFinitistic.OrdinarySimulation.TerminalSimple.tower _root_.OAI.LittleFinitistic.OrdinarySimulation.XResolution.rightTerm_projective _root_.OAI.LittleFinitistic.PDBarQuotient.leftModule _root_.OAI.LittleFinitistic.SelectedBaseIterates.input_finite _root_.OAI.LittleFinitistic.SelectedBaseIterates.input_finiteD _root_.OAI.LittleFinitistic.SelectedFirstBlockFamily.derivedInflation_additive _root_.OAI.LittleFinitistic.SelectedFirstBlockFamily.inflation_preservesFiniteColimits _root_.OAI.LittleFinitistic.SelectedFirstBlockFamily.inflation_preservesFiniteLimits _root_.OAI.LittleFinitistic.SelectedOrdinaryModules.instFiniteAInflated _root_.OAI.LittleFinitistic.SelectedOrdinaryModules.instIsScalarTowerComplexAInflated _root_.OAI.LittleFinitistic.SelectedOrdinaryModules.instIsScalarTowerComplexBPInflated _root_.OAI.LittleFinitistic.SelectedOrdinaryModules.instIsScalarTowerComplexDInflated _root_.OAI.LittleFinitistic.SelectedOrdinaryModules.instModuleAInflated _root_.OAI.LittleFinitistic.SelectedOrdinaryModules.instModuleBComplexPInflated _root_.OAI.LittleFinitistic.SelectedOrdinaryModules.instModuleDInflated _root_.OAI.LittleFinitistic.SelectedPDDetection.residueModuleK _root_.OAI.LittleFinitistic.SelectedTensor.comparison_isIso
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory
namespace LittleFinitistic.SelectedOrdinaryDimension
open SelectedOrdinaryAlgebra SelectedFixedDiagram

/-- The actual D has the manuscript's global dimension bound on both sides. -/
theorem both_sides :
    (⨆ M : ModuleCat.{0} D, projectiveDimension M) ≤ bound ∧
    (⨆ M : ModuleCat.{0} Dᵐᵒᵖ, projectiveDimension M) ≤ bound :=
  OrdinarySimulation.source_ordinary_globalDimension_bound (QuadraticEncoding.composition P) length

theorem left_module (M : ModuleCat.{0} D) : HasProjectiveDimensionLE M bound := by
  apply (projectiveDimension_le_iff M bound).mp
  exact (le_iSup (fun N : ModuleCat.{0} D => projectiveDimension N) M).trans both_sides.1

end LittleFinitistic.SelectedOrdinaryDimension

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Selected_SelectedFiniteAmplitude
attribute [-instance] _root_.OAI.LittleFinitistic.BimoduleTotal.augmentationComparisonOnChains_isIso _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.OrdinarySimulation.BimoduleO.commuteRightTensor _root_.OAI.LittleFinitistic.OrdinarySimulation.TensorResolution.augmentation_epi _root_.OAI.LittleFinitistic.OrdinarySimulation.TensorResolution.integerBimoduleRight_projective _root_.OAI.LittleFinitistic.OrdinarySimulation.TensorResolution.integerTerm_moduleProjective _root_.OAI.LittleFinitistic.OrdinarySimulation.TensorResolution.projectiveTerm _root_.OAI.LittleFinitistic.OrdinarySimulation.TensorResolution.term_projective _root_.OAI.LittleFinitistic.OrdinarySimulation.TerminalSimple.instModuleMulOppositeChainAlgebra _root_.OAI.LittleFinitistic.OrdinarySimulation.TerminalSimple.tower _root_.OAI.LittleFinitistic.OrdinarySimulation.XResolution.rightTerm_projective _root_.OAI.LittleFinitistic.PDBarQuotient.leftModule _root_.OAI.LittleFinitistic.SelectedFirstBlockFamily.derivedInflation_additive _root_.OAI.LittleFinitistic.SelectedFirstBlockFamily.inflation_preservesFiniteColimits _root_.OAI.LittleFinitistic.SelectedFirstBlockFamily.inflation_preservesFiniteLimits _root_.OAI.LittleFinitistic.SelectedPDDetection.residueModuleK
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory
namespace LittleFinitistic.SelectedFiniteAmplitude
open SelectedOrdinaryAlgebra SelectedBaseIterates

local instance instHasDerivedCategoryModuleCatD_r8d7edd_2 : HasDerivedCategory.{1} (ModuleCat.{0} D) :=
  HasDerivedCategory.standard (ModuleCat.{0} D)
/-- Every genuine X-derived iterate of each actual test input has finite amplitude.
The extra two degrees per iteration are harmless for the finite-dimension argument. -/
theorem bounded (Y : FiniteSelectionFamily.S.{0}) (r : ℕ) :
    (object Y r).IsGE (-((r * (3 * length + 4) : ℕ) : ℤ)) ∧
    (object Y r).IsLE 0 := by
  simpa only [SelectedOrdinaryDimension.bound, Nat.add_assoc] using
    SelectedBaseIterates.bounded SelectedOrdinaryDimension.bound
      SelectedOrdinaryDimension.left_module Y r

end LittleFinitistic.SelectedFiniteAmplitude

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Selected_SelectedCountCohomology
attribute [-instance] _root_.OAI.LittleFinitistic.BimoduleTotal.augmentationComparisonOnChains_isIso _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.OrdinarySimulation.BimoduleO.commuteRightTensor _root_.OAI.LittleFinitistic.OrdinarySimulation.TensorResolution.augmentation_epi _root_.OAI.LittleFinitistic.OrdinarySimulation.TensorResolution.integerBimoduleRight_projective _root_.OAI.LittleFinitistic.OrdinarySimulation.TensorResolution.integerTerm_moduleProjective _root_.OAI.LittleFinitistic.OrdinarySimulation.TensorResolution.projectiveTerm _root_.OAI.LittleFinitistic.OrdinarySimulation.TensorResolution.term_projective _root_.OAI.LittleFinitistic.OrdinarySimulation.TerminalSimple.instModuleMulOppositeChainAlgebra _root_.OAI.LittleFinitistic.OrdinarySimulation.TerminalSimple.tower _root_.OAI.LittleFinitistic.OrdinarySimulation.XResolution.rightTerm_projective _root_.OAI.LittleFinitistic.PDBarQuotient.leftModule _root_.OAI.LittleFinitistic.SelectedFirstBlockFamily.derivedInflation_additive _root_.OAI.LittleFinitistic.SelectedFirstBlockFamily.inflation_preservesFiniteColimits _root_.OAI.LittleFinitistic.SelectedFirstBlockFamily.inflation_preservesFiniteLimits _root_.OAI.LittleFinitistic.SelectedPDDetection.residueModuleK
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace LittleFinitistic.SelectedCountCohomology
open SelectedOrdinaryAlgebra SelectedBaseIterates

attribute [local instance] OAI.LittleFinitistic.SelectedCountCohomology.instHasDerivedCategoryModuleCatD
theorem isZero_iff (Y : FiniteSelectionFamily.S.{0}) (r : ℕ) :
    IsZero (count Y r) ↔ IsZero (object Y r) :=
  (comparison Y r).isZero_iff.symm.trans
    (ExternalTensor.Binomial.isZero_shift_iff (object Y r) (r : ℤ))

theorem bounded (Y : FiniteSelectionFamily.S.{0}) (r : ℕ) :
    (count Y r).IsGE (-((r * (3 * length + 5) : ℕ) : ℤ)) ∧
    (count Y r).IsLE (-(r : ℤ)) := by
  have := (SelectedFiniteAmplitude.bounded Y r).1
  have := (SelectedFiniteAmplitude.bounded Y r).2
  have : ((object Y r)⟦(r : ℤ)⟧).IsGE (-((r * (3 * length + 5) : ℕ) : ℤ)) := by
    apply DerivedCategory.TStructure.t.isGE_shift (object Y r)
      (-((r * (3 * length + 4) : ℕ) : ℤ)) (r : ℤ)
      (-((r * (3 * length + 5) : ℕ) : ℤ)) ?_
    push_cast
    ring
  have : ((object Y r)⟦(r : ℤ)⟧).IsLE (-(r : ℤ)) :=
    DerivedCategory.TStructure.t.isLE_shift (object Y r) 0 (r : ℤ) (-(r : ℤ)) (by omega)
  exact ⟨DerivedCategory.TStructure.t.isGE_of_iso (comparison Y r) _,
    DerivedCategory.TStructure.t.isLE_of_iso (comparison Y r) _⟩

/-- Every surviving iterate contributes a nonzero original count class in a
homological degree at least r, with an explicit finite upper bound. -/
theorem nonzero_degree (Y : FiniteSelectionFamily.S.{0}) (r : ℕ)
    (h : ¬ IsZero (object Y r)) :
    ∃ n : ℕ, r ≤ n ∧ n ≤ r * (3 * length + 5) ∧
      ¬ IsZero ((DerivedCategory.homologyFunctor (ModuleCat D) (-(n : ℤ))).obj (count Y r)) := by
  have := (bounded Y r).1
  have := (bounded Y r).2
  by_contra hn
  push Not at hn
  have hz (i : ℤ) : IsZero ((DerivedCategory.homologyFunctor (ModuleCat D) i).obj (count Y r)) := by
    by_cases hi : i ≤ 0
    · obtain ⟨n,rfl⟩ := Int.exists_eq_neg_ofNat hi
      by_cases hlo : r ≤ n
      · by_cases hhi : n ≤ r * (3 * length + 5)
        · exact hn n hlo hhi
        · exact DerivedCategory.isZero_of_isGE _ (-((r * (3 * length + 5) : ℕ) : ℤ))
            (-(n : ℤ)) (by omega)
      · exact DerivedCategory.isZero_of_isLE _ (-(r : ℤ)) (-(n : ℤ)) (by omega)
    · exact DerivedCategory.isZero_of_isLE _ (-(r : ℤ)) i (by omega)
  have : (count Y r).IsLE (-1) := (DerivedCategory.isLE_iff _ _).mpr (fun i _ => hz i)
  have : (count Y r).IsGE 0 := (DerivedCategory.isGE_iff _ _).mpr (fun i _ => hz i)
  apply h
  apply (isZero_iff Y r).mp
  apply (IsZero.iff_id_eq_zero _).mpr
  exact DerivedCategory.TStructure.t.zero (𝟙 _) (-1) 0 (by omega)
end LittleFinitistic.SelectedCountCohomology

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Selected_SelectedCountExtinction
attribute [-instance] _root_.OAI.LittleFinitistic.BimoduleTotal.augmentationComparisonOnChains_isIso _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.OrdinarySimulation.BimoduleO.commuteRightTensor _root_.OAI.LittleFinitistic.OrdinarySimulation.TensorResolution.augmentation_epi _root_.OAI.LittleFinitistic.OrdinarySimulation.TensorResolution.integerBimoduleRight_projective _root_.OAI.LittleFinitistic.OrdinarySimulation.TensorResolution.integerTerm_moduleProjective _root_.OAI.LittleFinitistic.OrdinarySimulation.TensorResolution.projectiveTerm _root_.OAI.LittleFinitistic.OrdinarySimulation.TensorResolution.term_projective _root_.OAI.LittleFinitistic.OrdinarySimulation.TerminalSimple.instModuleMulOppositeChainAlgebra _root_.OAI.LittleFinitistic.OrdinarySimulation.TerminalSimple.tower _root_.OAI.LittleFinitistic.OrdinarySimulation.XResolution.rightTerm_projective _root_.OAI.LittleFinitistic.PDBarQuotient.leftModule _root_.OAI.LittleFinitistic.SelectedFirstBlockFamily.derivedInflation_additive _root_.OAI.LittleFinitistic.SelectedFirstBlockFamily.inflation_preservesFiniteColimits _root_.OAI.LittleFinitistic.SelectedFirstBlockFamily.inflation_preservesFiniteLimits _root_.OAI.LittleFinitistic.SelectedPDDetection.residueModuleK
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace LittleFinitistic.SelectedCountExtinction
open SelectedOrdinaryAlgebra SelectedBaseIterates SelectedCountCohomology

attribute [local instance] OAI.LittleFinitistic.SelectedCountExtinction.instHasDerivedCategoryModuleCatD
/-- After actual tensor extinction, all later original count summands vanish. -/
theorem tail_zero (Y : FiniteSelectionFamily.S.{0}) (t r : ℕ) (htr : t ≤ r)
    (h : IsZero (object Y t)) : IsZero (count Y r) :=
  (SelectedCountCohomology.isZero_iff Y r).mpr
    (DerivedBar.IterateSupport.zero_of_le ℂ D X (input Y) t r htr h)

/-- A zero iterate gives one finite cohomological window for the entire original
count family, including the infinitely many counts that have already vanished. -/
theorem uniform_bounded (Y : FiniteSelectionFamily.S.{0}) (t : ℕ)
    (h : IsZero (object Y t)) (r : ℕ) :
    (count Y r).IsGE (-((t * (3 * length + 5) : ℕ) : ℤ)) ∧ (count Y r).IsLE 0 := by
  have := (SelectedCountCohomology.bounded Y r).1
  have := (SelectedCountCohomology.bounded Y r).2
  constructor
  · by_cases htr : t ≤ r
    · apply (DerivedCategory.isGE_iff _ _).mpr
      intro i _
      exact (DerivedCategory.homologyFunctor (ModuleCat D) i).map_isZero (tail_zero Y t r htr h)
    · apply DerivedCategory.TStructure.t.isGE_of_ge (count Y r)
        (-((t * (3 * length + 5) : ℕ) : ℤ)) (-((r * (3 * length + 5) : ℕ) : ℤ)) ?_
      have hm := Nat.mul_le_mul_right (3 * length + 5) (show r ≤ t by omega)
      exact neg_le_neg (by exact_mod_cast hm)
  · exact DerivedCategory.TStructure.t.isLE_of_le (count Y r) (-(r : ℤ)) 0 (by omega)

/-- Every original count has zero cohomology outside that single finite window. -/
theorem uniform_homology_zero (Y : FiniteSelectionFamily.S.{0}) (t : ℕ)
    (h : IsZero (object Y t)) (r : ℕ) (i : ℤ)
    (hi : i < -((t * (3 * length + 5) : ℕ) : ℤ) ∨ 0 < i) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat D) i).obj (count Y r)) := by
  have := (uniform_bounded Y t h r).1
  have := (uniform_bounded Y t h r).2
  exact hi.elim (fun h => DerivedCategory.isZero_of_isGE _ _ i h)
    (fun h => DerivedCategory.isZero_of_isLE _ 0 i h)
end LittleFinitistic.SelectedCountExtinction

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Selected_SelectedPDBarConsumer
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.OrdinarySimulation.BimoduleO.commuteRightTensor _root_.OAI.LittleFinitistic.OrdinarySimulation.TensorResolution.augmentation_epi _root_.OAI.LittleFinitistic.OrdinarySimulation.TensorResolution.integerBimoduleRight_projective _root_.OAI.LittleFinitistic.OrdinarySimulation.TensorResolution.integerTerm_moduleProjective _root_.OAI.LittleFinitistic.OrdinarySimulation.TensorResolution.projectiveTerm _root_.OAI.LittleFinitistic.OrdinarySimulation.TensorResolution.term_projective _root_.OAI.LittleFinitistic.OrdinarySimulation.TerminalSimple.instModuleMulOppositeChainAlgebra _root_.OAI.LittleFinitistic.OrdinarySimulation.TerminalSimple.tower _root_.OAI.LittleFinitistic.OrdinarySimulation.XResolution.rightTerm_projective _root_.OAI.LittleFinitistic.SelectedBaseIterates.input_finite _root_.OAI.LittleFinitistic.SelectedBaseIterates.input_finiteD _root_.OAI.LittleFinitistic.SelectedFirstBlockFamily.derivedInflation_additive _root_.OAI.LittleFinitistic.SelectedFirstBlockFamily.inflation_preservesFiniteColimits _root_.OAI.LittleFinitistic.SelectedFirstBlockFamily.inflation_preservesFiniteLimits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace LittleFinitistic.SelectedPDDetection
open SelectedOrdinaryAlgebra SelectedOrdinaryModules

theorem lower_bound_of_base_bar (Y : FiniteSelectionFamily.S.{0})
    (r n : ℕ) (hrn : r ≤ n) (h : ¬ IsZero ((baseBar Y).homology n)) :
    r ≤ projectiveDimension (module Y) :=
  PDBarQuotient.lower_bound_of_base_bar augmentation (Inflated Y) r n hrn h

end LittleFinitistic.SelectedPDDetection

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Selected_SelectedPDResidueProjection
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.OrdinarySimulation.BimoduleO.commuteRightTensor _root_.OAI.LittleFinitistic.OrdinarySimulation.TensorResolution.augmentation_epi _root_.OAI.LittleFinitistic.OrdinarySimulation.TensorResolution.integerBimoduleRight_projective _root_.OAI.LittleFinitistic.OrdinarySimulation.TensorResolution.integerTerm_moduleProjective _root_.OAI.LittleFinitistic.OrdinarySimulation.TensorResolution.projectiveTerm _root_.OAI.LittleFinitistic.OrdinarySimulation.TensorResolution.term_projective _root_.OAI.LittleFinitistic.OrdinarySimulation.TerminalSimple.instModuleMulOppositeChainAlgebra _root_.OAI.LittleFinitistic.OrdinarySimulation.TerminalSimple.tower _root_.OAI.LittleFinitistic.OrdinarySimulation.XResolution.rightTerm_projective _root_.OAI.LittleFinitistic.PDBarQuotient.leftModule _root_.OAI.LittleFinitistic.SelectedBaseIterates.input_finite _root_.OAI.LittleFinitistic.SelectedBaseIterates.input_finiteD _root_.OAI.LittleFinitistic.SelectedFirstBlockFamily.derivedInflation_additive _root_.OAI.LittleFinitistic.SelectedFirstBlockFamily.inflation_preservesFiniteColimits _root_.OAI.LittleFinitistic.SelectedFirstBlockFamily.inflation_preservesFiniteLimits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace LittleFinitistic.SelectedPDDetection
open SelectedOrdinaryAlgebra SelectedOrdinaryModules

theorem augmentation_surjective : Function.Surjective augmentation :=
  fun d => ⟨TrivSqZeroExt.inl d, rfl⟩

theorem augmentation_kernel_square_zero :
    ∀ a ∈ RingHom.ker augmentation.toRingHom, ∀ b ∈ RingHom.ker augmentation.toRingHom, a*b=0 :=
  fun a ha b hb => PDSquareZero.kernel_square_zero X a b ha hb

end LittleFinitistic.SelectedPDDetection

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Selected_SelectedPDUpperConsumer
attribute [-instance] _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.OrdinarySimulation.BimoduleO.commuteRightTensor _root_.OAI.LittleFinitistic.OrdinarySimulation.TensorResolution.augmentation_epi _root_.OAI.LittleFinitistic.OrdinarySimulation.TensorResolution.integerBimoduleRight_projective _root_.OAI.LittleFinitistic.OrdinarySimulation.TensorResolution.integerTerm_moduleProjective _root_.OAI.LittleFinitistic.OrdinarySimulation.TensorResolution.projectiveTerm _root_.OAI.LittleFinitistic.OrdinarySimulation.TensorResolution.term_projective _root_.OAI.LittleFinitistic.OrdinarySimulation.TerminalSimple.instModuleMulOppositeChainAlgebra _root_.OAI.LittleFinitistic.OrdinarySimulation.TerminalSimple.tower _root_.OAI.LittleFinitistic.OrdinarySimulation.XResolution.rightTerm_projective _root_.OAI.LittleFinitistic.SelectedFirstBlockFamily.derivedInflation_additive _root_.OAI.LittleFinitistic.SelectedFirstBlockFamily.inflation_preservesFiniteColimits _root_.OAI.LittleFinitistic.SelectedFirstBlockFamily.inflation_preservesFiniteLimits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace LittleFinitistic.SelectedPDDetection
open SelectedOrdinaryAlgebra SelectedOrdinaryModules

local instance instHasDerivedCategoryModuleCatD_2_r8d7edd_1 : HasDerivedCategory.{1} (ModuleCat.{0} D) :=
  HasDerivedCategory.standard (ModuleCat.{0} D)
/-- For the fixed actual A and Inflated Y, bounded actual D-bar homology
implies finite projective dimension, using the proved global dimension of D. -/
theorem finite_pd_of_bounded_base_bar (Y : FiniteSelectionFamily.S.{0})
    (h : ∃ b : ℕ, ∀ n, b < n → IsZero
      ((DerivedBar.twoSidedComplex ℂ A D (Inflated Y) augmentation).homology n)) :
    projectiveDimension (module Y) < ⊤ :=
  PDResidueAssociativity.finite_pd_of_bounded_base_bar augmentation (Inflated Y)
    augmentation_surjective augmentation_kernel_square_zero
    SelectedOrdinaryDimension.bound SelectedOrdinaryDimension.left_module h

end LittleFinitistic.SelectedPDDetection

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Selected_SelectedPDConclusion
attribute [-instance] _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleTotal.augmentationComparisonOnChains_isIso _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.OrdinarySimulation.BimoduleO.commuteRightTensor _root_.OAI.LittleFinitistic.OrdinarySimulation.TensorResolution.augmentation_epi _root_.OAI.LittleFinitistic.OrdinarySimulation.TensorResolution.integerBimoduleRight_projective _root_.OAI.LittleFinitistic.OrdinarySimulation.TensorResolution.integerTerm_moduleProjective _root_.OAI.LittleFinitistic.OrdinarySimulation.TensorResolution.projectiveTerm _root_.OAI.LittleFinitistic.OrdinarySimulation.TensorResolution.term_projective _root_.OAI.LittleFinitistic.OrdinarySimulation.TerminalSimple.instModuleMulOppositeChainAlgebra _root_.OAI.LittleFinitistic.OrdinarySimulation.TerminalSimple.tower _root_.OAI.LittleFinitistic.OrdinarySimulation.XResolution.rightTerm_projective _root_.OAI.LittleFinitistic.SelectedFirstBlockFamily.derivedInflation_additive _root_.OAI.LittleFinitistic.SelectedFirstBlockFamily.inflation_preservesFiniteColimits _root_.OAI.LittleFinitistic.SelectedFirstBlockFamily.inflation_preservesFiniteLimits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace LittleFinitistic.SelectedPDConclusion
open SelectedOrdinaryAlgebra SelectedOrdinaryModules

local instance instHasDerivedCategoryModuleCatD_r8d7edd_3 : HasDerivedCategory.{1} (ModuleCat.{0} D) :=
  HasDerivedCategory.standard (ModuleCat.{0} D)
/-- Actual tensor extinction implies finite projective dimension over the
one fixed square-zero algebra A. The bar bounds and minimal detector are proved. -/
theorem finite_pd_of_extinction (Y : FiniteSelectionFamily.S.{0}) (t : ℕ)
    (h : IsZero (SelectedBaseIterates.object Y t)) :
    projectiveDimension (module Y) < ⊤ := by
  apply SelectedPDDetection.finite_pd_of_bounded_base_bar Y
  refine ⟨t * (3 * length + 5), fun n hn => ?_⟩
  have hc := DerivedBar.ParityBridge.baseChangeTor_bounded_of_counts ℂ D X
    (SelectedBaseIterates.input Y) (t * (3 * length + 5))
    (fun r n hn => SelectedCountExtinction.uniform_homology_zero Y t h r (-(n : ℤ))
      (Or.inl (by omega))) n hn
  exact hc.of_iso (baseTorIso Y n).symm

/-- A surviving actual derived iterate supplies a nonzero original count
class and hence the manuscript's projective-dimension lower bound. -/
theorem lower_bound_of_survival (Y : FiniteSelectionFamily.S.{0}) (r : ℕ)
    (h : ¬ IsZero (SelectedBaseIterates.object Y r)) :
    (r : WithBot ℕ∞) ≤ projectiveDimension (module Y) := by
  obtain ⟨n,hrn,_,hn⟩ := SelectedCountCohomology.nonzero_degree Y r h
  have hc := DerivedBar.ParityBridge.baseChangeTor_nonzero_of_count ℂ D X
    (SelectedBaseIterates.input Y) r n hn
  apply SelectedPDDetection.lower_bound_of_base_bar Y r n hrn
  intro hz
  exact hc (hz.of_iso (baseTorIso Y n))

end LittleFinitistic.SelectedPDConclusion

end

end OAI
end

section
-- module Solutions.OAIQ023_Fin.Finitistic_Main
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace LittleFinitistic.Main
open SelectedOrdinaryAlgebra SelectedOrdinaryModules

/-- For the one fixed finite-dimensional complex algebra constructed in the
manuscript, every positive m has the actual finite module N_m with the stated
finite projective-dimension bounds. -/
theorem projective_dimension_bounds (m : ℕ) [NeZero m] :
    ((2*m-2 : ℕ) : WithBot ℕ∞) ≤ projectiveDimension (testModule m) ∧
      projectiveDimension (testModule m) < ⊤ := by
  have h := SelectedOrdinaryOrbit.extinction m
  exact ⟨SelectedPDConclusion.lower_bound_of_survival (FiniteSelectionFamily.test m) (2*m-2) h.2,
    SelectedPDConclusion.finite_pd_of_extinction (FiniteSelectionFamily.test m) (2*m) h.1⟩

/-- The actual constructed algebra has infinite little finitistic dimension. -/
theorem infinite_littleFinitisticDimension : littleFinitisticDimension A = ⊤ := by
  apply littleFinitisticDimension_eq_top_of_two_mul_bounds
  intro m hm
  let : NeZero m := ⟨by omega⟩
  exact ⟨testModule m, inferInstance, (projective_dimension_bounds m).2,
    (projective_dimension_bounds m).1⟩

/-- Main theorem, with finite dimensionality of the one fixed A explicit and
with actual finitely generated witness modules for every positive m. -/
theorem counterexample : FiniteDimensional ℂ A ∧ littleFinitisticDimension A = ⊤ ∧
    ∀ m : ℕ, 0 < m → ∃ N : ModuleCat.{0} A, Module.Finite A N ∧
      ((2*m-2 : ℕ) : WithBot ℕ∞) ≤ projectiveDimension N ∧ projectiveDimension N < ⊤ := by
  refine ⟨inferInstance, infinite_littleFinitisticDimension, ?_⟩
  intro m hm
  let : NeZero m := ⟨by omega⟩
  exact ⟨testModule m, inferInstance, projective_dimension_bounds m⟩

theorem exists_counterexample_oai :
    ∃ (A : Type) (_ : Ring A) (_ : Algebra ℂ A),
      FiniteDimensional ℂ A ∧ littleFinitisticDimension A = ⊤ ∧
        ∀ m : ℕ, 0 < m → ∃ N : ModuleCat.{0} A, Module.Finite A N ∧
          ((2*m-2 : ℕ) : WithBot ℕ∞) ≤ projectiveDimension N ∧
            projectiveDimension N < ⊤ := by
  exact ⟨SelectedOrdinaryAlgebra.A, inferInstance, inferInstance, counterexample⟩

end LittleFinitistic.Main

end

end OAI
end

theorem solution : type_of% @OAI.LittleFinitistic.Main.exists_counterexample_oai := @OAI.LittleFinitistic.Main.exists_counterexample_oai
