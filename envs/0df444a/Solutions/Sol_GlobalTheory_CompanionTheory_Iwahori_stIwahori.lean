-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Iwahori.stIwahori
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:40:09.854332+00:00
-- url     : https://prove2.me/submissions/bf9e968e-6555-4b7e-b2b6-8476c9e58cbc

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_StSandwich
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_IsCongIdealTwoTorsion
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_IsPiecesPiece
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_IwahoriUpperLowerFactorizationStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_AntiInvolutionSwapsUpperLowerStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_TorusConjugationPreservesCongruenceStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_HermitianAdjointExistsStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_CongruenceEndomorphismInverseExistsStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_UpperTriangularInverseIsUpperStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_IwahoriStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_Iwahori_isCongIdeal_congJ
import Theorems.Thm_GlobalTheory_CompanionTheory_Iwahori_congJ_smul
import Theorems.Thm_GlobalTheory_CompanionTheory_Iwahori_isUpper_rev_iff
import Theorems.Thm_GlobalTheory_CompanionTheory_Iwahori_eq_of_pair
import Theorems.Thm_GlobalTheory_CompanionTheory_Iwahori_exists_star
import Theorems.Thm_GlobalTheory_CompanionTheory_Iwahori_isPieces_piece
import Theorems.Thm_GlobalTheory_CompanionTheory_Iwahori_piece_mem
import Theorems.Thm_GlobalTheory_CompanionTheory_Iwahori_rev_rev
import Theorems.Thm_GlobalTheory_CompanionTheory_Iwahori_tau_mono
import Theorems.Thm_GlobalTheory_CompanionTheory_Iwahori_tau_ne
import Theorems.Thm_GlobalTheory_CompanionTheory_Iwahori_tor_piece
import Theorems.Thm_GlobalTheory_CompanionTheory_Iwahori_wt_injective
import Theorems.Thm_GlobalTheory_CompanionTheory_Iwahori_wt_rev
import Theorems.Thm_GlobalTheory_T_hermitian_adjoint_exists
import Theorems.Thm_GlobalTheory_T_iwahori_upper_lower_factorization
import Theorems.Thm_GlobalTheory_T_torus_conjugation_preserves_congruence
import Theorems.Thm_GlobalTheory_T_unitary_factors_of_unitary_upper_mul_lowerUni
import Theorems.Thm_GlobalTheory_T_upper_triangular_inverse_is_upper


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CompanionTheory.Rg.FlB
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Iwahori
namespace GlobalTheory.CompanionTheory.Iwahori
theorem _root_.solution : StIwahori := by
  intro L _ _ _ _ s hs δ hδ V _ _ _ h hh l e f W Λ hF hΛ hA π hπ k hk hc
  have hδ0 : δ ≠ 0 := hδ.1
  set P := piece hh δ e f with hPdef
  have hP : IsPieces P := isPieces_piece hh hδ0 hF
  have hJ : IsCongIdeal (congJ Λ π) P :=
    isCongIdeal_congJ hΛ hπ P fun i x hx => piece_mem hΛ hA hh hδ0 hF i hx
  obtain ⟨st, hst, st_mul, st_one, st_zero, st_P⟩ :=
    exists_star (δ := δ) (e := e) (f := f) (l := l) hs hh (GlobalTheory.T.hermitian_adjoint_exists s hs h hh)
  have hk1 : (k.toLinearMap : Module.End L V) - 1 ∈ congJ Λ π := fun x hx => by
    obtain ⟨y, hy, e1⟩ := hc x hx
    exact ⟨y, hy, by simpa using e1⟩
  obtain ⟨a, b, ha, hb, hup, hlo, hab⟩ := GlobalTheory.T.iwahori_upper_lower_factorization wt wt_injective P hP _ hJ _ hk1

  obtain ⟨ya, hya, ia1, ia2⟩ := hJ.inv _ ha
  obtain ⟨yb, hyb, ib1, ib2⟩ := hJ.inv _ hb
  rw [add_sub_cancel] at ia1 ia2 ib1 ib2
  have hkk : ∀ y, st (k.toLinearMap) (k y) = y := fun y => by
    refine eq_of_pair hh fun x => ?_
    have := hst k.toLinearMap x (k y)
    simp only [LinearEquiv.coe_coe] at this
    rw [← this, hk x y]
  have hk2 : st (k.toLinearMap) * (k.toLinearMap) = 1 := by
    ext y; exact hkk y
  have hk3 : (k.toLinearMap : Module.End L V) * st (k.toLinearMap) = 1 := by
    ext y
    obtain ⟨z, rfl⟩ := k.surjective y
    simp [Module.End.mul_apply, hkk z]
  rw [hab] at hk2 hk3
  obtain ⟨ua, ub⟩ := GlobalTheory.T.unitary_factors_of_unitary_upper_mul_lowerUni wt P hP rev rev_rev
    (fun i j hij => by have := wt_rev i; have := wt_rev j; omega) wt_injective st st_mul st_one st_zero st_P
    (fun a a' h1 h2 h3 => GlobalTheory.T.upper_triangular_inverse_is_upper wt P hP a a' h1 h2 h3)
    (fun a a' h1 h2 h3 => (isUpper_rev_iff P a').1 (GlobalTheory.T.upper_triangular_inverse_is_upper _ P hP a a' h1 h2 ((isUpper_rev_iff P a).2 h3)))
    a (1 + ya) b (1 + yb) ia1 ia2 ib1 ib2 hup hlo hk2 hk3
  let A : V ≃ₗ[L] V := LinearEquiv.ofLinear a (1 + ya) ia1 ia2
  let B : V ≃ₗ[L] V := LinearEquiv.ofLinear b (1 + yb) ib1 ib2
  have isoOf : ∀ (g : V ≃ₗ[L] V), st (g.toLinearMap) * g.toLinearMap = 1 → IsIso h g := fun g hg x y => by
    have := hst g.toLinearMap x (g y)
    simp only [LinearEquiv.coe_coe] at this
    rw [this]
    have h2 : st g.toLinearMap (g y) = y := by
      have := congrArg (fun m : Module.End L V => m y) hg
      simpa [Module.End.mul_apply] using this
    rw [h2]
  refine ⟨A, B, isoOf A ua, isoOf B ub, ?_, ?_⟩
  · ext x
    have := congrArg (fun m : Module.End L V => m x) hab
    simpa [A, B, Module.End.mul_apply] using this
  · intro u t hu0 hm h1 ht
    have hT := fun i => tor_piece (δ := δ) hh hδ0 hF ht i
    have key := GlobalTheory.T.torus_conjugation_preserves_congruence wt P hP _ hJ (congJ_smul hΛ π) (t.toLinearMap) (t.symm.toLinearMap) (tau s u)
      (tau_ne hu0) (by ext y; simp [Module.End.mul_apply]) (by ext y; simp [Module.End.mul_apply])
      (fun i => (hT i).1) (fun i => (hT i).2)
      (tau_mono hs hu0 hm h1) a b ha hb hup hlo.1
    constructor
    · intro x hx
      obtain ⟨y, hy, e1⟩ := key.1 x hx
      exact ⟨y, hy, by simpa [A, Module.End.mul_apply] using e1⟩
    · intro x hx
      obtain ⟨y, hy, e1⟩ := key.2 x hx
      exact ⟨y, hy, by simpa [B, Module.End.mul_apply] using e1⟩
end GlobalTheory.CompanionTheory.Iwahori
