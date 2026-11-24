-- Prove2me | solution 1 for GlobalTheory.CuspGL.MassMult.mass_mult
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:02:55.563393+00:00
-- url     : https://prove2.me/submissions/682d05f7-9136-4385-a28a-ff71d0b202e7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_CharpolyBlockAndInvariantUnderStabilizerNilradicStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_FinsumSubspaceStabilizerMulBlockFunctionsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_CardSubspacesMulGeneralLinearGroupCardStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_EndomorphismMassEqOfLinearEquivInvariantStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_EndomorphismMassMulParabolicInductionTrivial
import Theorems.Thm_GlobalTheory_CuspGL_MassMult_finsum_subtype_dite
import Theorems.Thm_GlobalTheory_CuspGL_MassMult_mass_eq
import Theorems.Thm_GlobalTheory_CuspGL_MassMult_finite_pairs
import Theorems.Thm_GlobalTheory_CuspGL_MassMult_finite_end
import Theorems.Thm_GlobalTheory_CuspGL_MassMult_mass_eq_zero
import Theorems.Thm_GlobalTheory_CuspGL_MassMult_stab_sum
import Theorems.Thm_GlobalTheory_CuspGL_MassMult_glCard_ne_zero
import Theorems.Thm_GlobalTheory_T_card_subspaces_mul_generalLinearGroupCard
import Theorems.Thm_GlobalTheory_T_endomorphismMass_eq_of_linearEquiv_invariant


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial GlobalTheory.CuspGL
open GlobalTheory GlobalTheory.CuspGL GlobalTheory.CuspGL.MassMult
namespace GlobalTheory.CuspGL.MassMult
theorem _root_.solution : ∀ (F : Type) [Field F] [Finite F] (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V] (Φ : ∀ (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V], Module.End F V → ℂ), (∀ (V V' : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V] [AddCommGroup V'] [Module F V'] [FiniteDimensional F V'] (e : V ≃ₗ[F] V') (g : Module.End F V), Φ V' (e.conj g) = Φ V g) → ∀ P : F[X], P.Monic → P.natDegree = Module.finrank F V → mass (fun g : Module.End F V => ∑ᶠ W : {W : Submodule F V // ∀ x ∈ W, g x ∈ W}, Φ W.1 (g.restrict W.2)) P / glCard F P.natDegree = conv (fun D => mass (Φ (Fin D.natDegree → F)) D / glCard F D.natDegree) mu P := by
  classical
  intro F _ _ V _ _ _ Φ hΦ P hP hdeg
  have := finite_end F V
  have : Finite V := Module.finite_of_finite F
  have := Fintype.ofFinite (Module.End F V)
  have := Fintype.ofFinite (Submodule F V)
  have hfin := finite_pairs P hP
  have hT : ∀ x, x ∈ hfin.toFinset ↔ x.1.Monic ∧ x.2.Monic ∧ x.1 * x.2 = P := fun x => by
    rw [Set.Finite.mem_toFinset]; rfl
  have h1 : mass (fun g : Module.End F V => ∑ᶠ W : {W : Submodule F V // ∀ x ∈ W, g x ∈ W},
      Φ W.1 (g.restrict W.2)) P = ∑ W : Submodule F V,
      ∑ᶠ g : {g : Module.End F V // ∀ x ∈ W, g x ∈ W},
        (if LinearMap.charpoly g.1 = P then Φ W (g.1.restrict g.2) else 0) := by
    rw [mass_eq, finsum_eq_sum_of_fintype]
    simp only [finsum_subtype_dite]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun g _ => ?_
    by_cases hg : LinearMap.charpoly g = P
    · simp only [if_pos hg]
    · simp only [if_neg hg, dite_eq_ite, ite_self, Finset.sum_const_zero]
  rw [h1, conv, finsum_mem_eq_finite_toFinset_sum _ hfin]
  simp only [fun W : Submodule F V => stab_sum F V W (Φ W) P _ hT]
  rw [Finset.sum_comm, Finset.sum_div]
  refine Finset.sum_congr rfl ?_
  rintro ⟨D, E⟩ hx
  obtain ⟨hD, hE, hDE⟩ := (hT _).1 hx
  simp only at hD hE hDE ⊢
  have hsum : D.natDegree + E.natDegree = Module.finrank F V := by
    rw [← hdeg, ← hDE, hD.natDegree_mul hE]
  have h2 : ∀ W : Submodule F V, (Nat.card F : ℂ) ^ (Module.finrank F W * Module.finrank F (V ⧸ W)) *
      (mass (Φ W) D * mass (fun _ : Module.End F (V ⧸ W) => (1 : ℂ)) E) =
      if Module.finrank F W = D.natDegree then (Nat.card F : ℂ) ^ (D.natDegree * E.natDegree) *
        (mass (Φ (Fin D.natDegree → F)) D *
          mass (fun _ : Module.End F (Fin E.natDegree → F) => (1 : ℂ)) E) else 0 := by
    intro W
    by_cases hW : Module.finrank F W = D.natDegree
    · have hq : Module.finrank F (V ⧸ W) = E.natDegree := by
        have := Submodule.finrank_quotient_add_finrank W
        omega
      rw [if_pos hW, GlobalTheory.T.endomorphismMass_eq_of_linearEquiv_invariant F W Φ hΦ D hW.symm,
        GlobalTheory.T.endomorphismMass_eq_of_linearEquiv_invariant F (V ⧸ W) (fun _ _ _ _ _ => (1 : ℂ)) (fun _ _ _ _ _ _ _ _ _ _ => rfl) E hq.symm,
        hW, hq]
    · rw [if_neg hW, mass_eq_zero _ _ hW, zero_mul, mul_zero]
  have h3 := GlobalTheory.T.card_subspaces_mul_generalLinearGroupCard F V D.natDegree (by omega)
  have h4 : Module.finrank F V - D.natDegree = E.natDegree := by omega
  rw [h4, Nat.card_eq_fintype_card (α := {W : Submodule F V // Module.finrank F W = D.natDegree}),
    Fintype.card_subtype] at h3
  rw [Finset.sum_congr rfl fun W _ => h2 W, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, hdeg, mu]
  have g1 := glCard_ne_zero F D.natDegree
  have g2 := glCard_ne_zero F E.natDegree
  have g3 := glCard_ne_zero F (Module.finrank F V)
  rw [div_mul_div_comm, div_eq_div_iff g3 (mul_ne_zero g1 g2), ← h3]
  ring
end GlobalTheory.CuspGL.MassMult
