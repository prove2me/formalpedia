-- Prove2me | solution 1 for GlobalTheory.EigAdd.eigDim_add_transpose
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:38:02.95234+00:00
-- url     : https://prove2.me/submissions/4168f0d3-e740-4c13-b404-0e4f42288f9b

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartFH
import Definitions.Def_ReciprocityTheory_DualLattices_TowerZeroSurjective
import Definitions.Def_ReciprocityTheory_DualLattices_LinPairStatement
import Definitions.Def_ReciprocityTheory_DualLattices_LengthDegreeAbelianVariety
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_LePreimageOfNil
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Clauses
import Definitions.Def_ReciprocityTheory_DualLattices_SubMemOfCompat
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_Biextensions_GenericFiberCubeInclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsSeparatedOfIsQProjOver
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TeichmullerDepth_IsEigBasisIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_SquarefreeMapMinpolyInt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_EigenspaceDimAddSplitExactTranspose
import Theorems.Thm_GlobalTheory_order_rep_diagonalisable
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp
import Theorems.Thm_ReciprocityTheory_PGsh_L2_h1
import Theorems.Thm_ReciprocityTheory_PGsh_L2_h2
import Theorems.Thm_ReciprocityTheory_PGsh_L2_h3
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_succ_succ_alt
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_succ_zero_alt
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_zero_succ_alt
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_zero_zero_alt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_succ_succ_alt
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_succ_zero_alt
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_zero_succ_alt
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_zero_zero_alt


section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.EigAdd
private theorem trace_eq (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (OE : Type) [CommRing OE] [IsDomain OE]
    [CharZero OE] [Module.Free ℤ OE] [Module.Finite ℤ OE] [Fintype (OE →+* C)]
    (V : Type) [AddCommGroup V] [Module C V] [Module.Finite C V] (ρ : OE →+* Module.End C V) (a : OE) :
    LinearMap.trace C V (ρ a) = ∑ τ : OE →+* C,
      (Module.finrank C ↥(⨅ b : OE, Module.End.eigenspace (ρ b) (τ b)) : C) * τ a := by
  classical
  obtain ⟨h1, h2⟩ := (GlobalTheory.order_rep_diagonalisable C OE).2 V ρ
  have hI := DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top h1 h2
  have hv : ∀ (τ : OE →+* C) (v : V), v ∈ (⨅ b : OE, Module.End.eigenspace (ρ b) (τ b)) → ρ a v = τ a • v :=
    fun τ v hv => Module.End.mem_eigenspace_iff.1 ((Submodule.mem_iInf _).1 hv a)
  have hf : ∀ τ : OE →+* C, Set.MapsTo (ρ a) ↑(⨅ b : OE, Module.End.eigenspace (ρ b) (τ b))
      ↑(⨅ b : OE, Module.End.eigenspace (ρ b) (τ b)) := fun τ v h => by
    have h' : v ∈ (⨅ b : OE, Module.End.eigenspace (ρ b) (τ b)) := h
    have := Submodule.smul_mem _ (τ a) h'
    rw [← hv τ v h'] at this
    exact this
  rw [LinearMap.trace_eq_sum_trace_restrict hI hf]
  refine Finset.sum_congr rfl fun τ _ => ?_
  have : (ρ a).restrict (hf τ) = τ a • LinearMap.id := by
    ext v
    exact hv τ v.1 v.2
  rw [this, map_smul, LinearMap.trace_id, smul_eq_mul, mul_comm]
private theorem trace_mat (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (O : Type) [CommRing O] [Algebra O C]
    (OE : Type) [CommRing OE] [IsDomain OE]
    [CharZero OE] [Module.Free ℤ OE] [Module.Finite ℤ OE] [Fintype (OE →+* C)] (d : ℕ)
    (ρ : OE →+* Matrix (Fin d) (Fin d) O) (a : OE) :
    algebraMap O C (ρ a).trace = ∑ τ : OE →+* C, (eigDim C ρ τ : C) * τ a := by
  have := trace_eq C OE (Fin d → C)
    ((Matrix.toLinAlgEquiv' (R := C) (n := Fin d)).toRingEquiv.toRingHom.comp
      ((algebraMap O C).mapMatrix.comp ρ)) a
  refine Eq.trans ?_ this
  change _ = LinearMap.trace C _ (Matrix.toLin' ((ρ a).map (algebraMap O C)))
  rw [Matrix.trace_toLin'_eq, ← AddMonoidHom.map_trace]
private theorem coeff_eq (C : Type) [Field C] [CharZero C] (OE : Type) [CommRing OE] [Fintype (OE →+* C)]
    (m n : (OE →+* C) → ℕ) (h : ∀ a, ∑ τ : OE →+* C, (m τ : C) * τ a = ∑ τ : OE →+* C, (n τ : C) * τ a)
    (τ : OE →+* C) : m τ = n τ := by
  have li : LinearIndependent C (fun τ : OE →+* C => (τ : OE → C)) :=
    (linearIndependent_monoidHom OE C).comp (fun τ : OE →+* C => (τ : OE →* C))
      RingHom.coe_monoidHom_injective
  have := Fintype.linearIndependent_iffₛ.1 li (fun τ => (m τ : C)) (fun τ => (n τ : C))
    (by funext a; simpa [Finset.sum_apply] using h a) τ
  exact_mod_cast this
end GlobalTheory.EigAdd
end

set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.EigAdd
namespace GlobalTheory.EigAdd
theorem _root_.solution : ∀ (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (O : Type) [CommRing O] [Algebra O C] (OE : Type) [CommRing OE] [IsDomain OE] [CharZero OE] [Module.Free ℤ OE] [Module.Finite ℤ OE] (d r g : ℕ) (A : Matrix (Fin d) (Fin r) O) (B : Matrix (Fin g) (Fin d) O), SplitEx A B → ∀ (ρ : OE →+* Matrix (Fin d) (Fin d) O) (ρA : OE →+* Matrix (Fin r) (Fin r) O) (ρB : OE →+* Matrix (Fin g) (Fin g) O), (∀ a, B * ρ a = ρB a * B) → (∀ a, ρ a * A = A * ρA a) → ∀ τ : OE →+* C, eigDim C ρ τ = eigDim C ρA τ + eigDim C ρB τ ∧ eigDim C (fun a => (ρ a)ᵀ) τ = eigDim C ρ τ := by
  intro C _ _ _ O _ _ OE _ _ _ _ _ d r g A B hS ρ ρA ρB hB hA τ
  haveI : Finite (OE →+* C) := (GlobalTheory.order_rep_diagonalisable C OE).1
  letI : Fintype (OE →+* C) := Fintype.ofFinite _
  obtain ⟨-, A', B', h1, h2, h3⟩ := hS
  constructor
  · refine coeff_eq C OE (fun τ => eigDim C ρ τ) (fun τ => eigDim C ρA τ + eigDim C ρB τ) (fun a => ?_) τ
    have ht : (ρ a).trace = (ρA a).trace + (ρB a).trace := by
      have e1 : (ρ a * (A * A')).trace = (ρA a).trace := by
        rw [← Matrix.mul_assoc, hA, Matrix.trace_mul_comm, ← Matrix.mul_assoc, h1, Matrix.one_mul]
      have e2 : (ρ a * (B' * B)).trace = (ρB a).trace := by
        rw [← Matrix.mul_assoc, Matrix.trace_mul_comm, ← Matrix.mul_assoc, hB, Matrix.mul_assoc, h2,
          Matrix.mul_one]
      rw [← e1, ← e2, ← Matrix.trace_add, ← Matrix.mul_add, h3, Matrix.mul_one]
    simp only [Nat.cast_add, add_mul, Finset.sum_add_distrib]
    rw [← trace_mat, ← trace_mat, ← trace_mat, ht, map_add]
  · refine coeff_eq C OE (fun τ => eigDim C (trHom ρ) τ) (fun τ => eigDim C ρ τ) (fun a => ?_) τ
    rw [← trace_mat, ← trace_mat]
    exact congrArg _ (Matrix.trace_transpose _)
end GlobalTheory.EigAdd
