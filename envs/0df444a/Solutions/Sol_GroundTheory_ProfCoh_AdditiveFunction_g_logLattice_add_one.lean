-- Prove2me | solution 1 for GroundTheory.ProfCoh.AdditiveFunction.g_logLattice_add_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:32:58.889655+00:00
-- url     : https://prove2.me/submissions/66cc9d0c-3205-4b07-afa5-30b5a6417e1e

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_GlobalEulerCharacteristic_UnitsDefs
import Definitions.Def_GroundTheory_ProfiniteCohomology_LocalEulerCharacteristic_ModNEquivOfSurjectiveApplyModNRep
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_SUnits
import Definitions.Def_GroundTheory_ProfiniteCohomology_GlobalEulerCharacteristic_GEqAddOfExactOfFiniteCokernel
import Theorems.Thm_GroundTheory_ProfCoh_finite_modN_of_moduleFinite
import Theorems.Thm_GroundTheory_ProfCoh_finite_torsN_of_moduleFinite
import Theorems.Thm_GroundTheory_ProfCoh_AdditiveFunction_g_funPermRep
import Theorems.Thm_GroundTheory_ProfCoh_exists_logLatticeProd_intertwiner
import Theorems.Thm_GroundTheory_Global_finite_quotient_of_smul_mem
import Theorems.Thm_GroundTheory_ProfCoh_AdditiveFunction_g_add
import Theorems.Thm_GroundTheory_ProfCoh_AdditiveFunction_g_of_trivial_int
import Theorems.Thm_GroundTheory_ProfCoh_finite_modN_uliftInt
import Theorems.Thm_GroundTheory_ProfCoh_finite_torsN_uliftInt
import Theorems.Thm_P2M_GroundTheory_ProfCoh_AdditiveFunction_g_eq_of_finite_cokernel__fa6a384fcd8d
import Theorems.Thm_P2M_UpperTheory_Reformulated_B_AdicCompleteRootExistence_exists_root_of_dvd__8130b8fccf10
import Theorems.Thm_P2M_UpperTheory_Reformulated_B_CyclicSubtraction_apply_eq_of_cycSub_eq_zero__fe379387d69c


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.ProfCoh
universe u v
open NumberField NumberField.Units NumberField.InfinitePlace IsDedekindDomain Module
open GroundTheory.Global
open scoped TensorProduct
open GroundTheory.ProfCoh.AdditiveFunction
variable {K L : Type u} [Field K] [Field L] [NumberField L] [Algebra K L]
  {l : ℕ} [NeZero l] (d : AdditiveFunction.{u} l (L ≃ₐ[K] L))
namespace GroundTheory.ProfCoh.AdditiveFunction
theorem _root_.solution :
    letI := repAction (logLatticeRep K L)
    d.g (logLattice L) + d.one =
      d.toFun (InfinitePlace L → ZMod l) (funPermRep (ZMod l) (L ≃ₐ[K] L) (InfinitePlace L)) := by
  let _ := repAction (logLatticeRep K L)
  let _ := trivialIntAction.{u} (L ≃ₐ[K] L)
  let _ := repAction (funPermRep ℤ (L ≃ₐ[K] L) (InfinitePlace L))
  obtain ⟨φ, hφi, ⟨n, hn, hφn⟩, hφγ⟩ := exists_logLatticeProd_intertwiner (K := K) (L := L)
  let ψ : logLattice L × ULift.{u} ℤ →+ (InfinitePlace L → ℤ) :=
    φ.toAddMonoidHom.comp ((AddMonoidHom.id _).prodMap AddEquiv.ulift.toAddMonoidHom)
  have hψ : ∀ x, ψ x = φ (x.1, x.2.down) := fun _ ↦ rfl
  have hψi : Function.Injective ψ := by
    intro x y h
    rw [hψ, hψ] at h
    have h' := hφi h
    exact _root_.Prod.ext (Prod.mk.inj h').1 (ULift.ext _ _ (Prod.mk.inj h').2)
  have hψγ : ∀ (γ : L ≃ₐ[K] L) x, ψ (γ • x) = γ • ψ x := by
    intro γ x
    change φ (logLatticeRep K L γ x.1, x.2.down) =
      funPermRep ℤ (L ≃ₐ[K] L) (InfinitePlace L) γ (φ (x.1, x.2.down))
    rw [← hφγ]
    rfl
  have : Finite ((InfinitePlace L → ℤ) ⧸ ψ.range) :=
    finite_quotient_of_smul_mem _ hn fun y ↦ by
      obtain ⟨x, hx⟩ := hφn y
      exact ⟨(x.1, ULift.up x.2), hx⟩
  have := finite_modN_of_moduleFinite (A := InfinitePlace L → ℤ) l
  have := finite_torsN_of_moduleFinite (A := InfinitePlace L → ℤ) l
  have := finite_modN_of_moduleFinite (A := logLattice L) l
  have := finite_torsN_of_moduleFinite (A := logLattice L) l
  have := finite_modN_uliftInt.{u} l
  have := finite_torsN_uliftInt.{u} l
  rw [← d.g_funPermRep (InfinitePlace L), d.g_eq_of_finite_cokernel' ψ hψγ hψi,
    d.g_add (AddMonoidHom.inl (logLattice L) (ULift.{u} ℤ))
      (AddMonoidHom.snd (logLattice L) (ULift.{u} ℤ))
      (fun γ a ↦ _root_.Prod.ext rfl (smul_zero γ).symm) (fun _ _ ↦ rfl)
      (fun a b h ↦ congrArg Prod.fst h) ?_ (fun t ↦ ⟨(0, t), rfl⟩),
    d.g_of_trivial_int (ULift.{u} ℤ) (fun _ _ ↦ rfl) AddEquiv.ulift]
  rintro ⟨a, t⟩
  constructor
  · intro ht
    change t = 0 at ht
    exact ⟨a, by rw [ht]; rfl⟩
  · rintro ⟨a', h⟩
    rw [← h]
    rfl
end GroundTheory.ProfCoh.AdditiveFunction
