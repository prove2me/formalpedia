-- Prove2me | solution 1 for GlobalTheory.HL.mass_orbit_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:01:51.002805+00:00
-- url     : https://prove2.me/submissions/7f6f5223-216d-4704-baef-3b12606848c9

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_InvVolMulPosLeConj
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_OrbitMassEquivariantConstantFibreStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_OrbitMassEqInvStabilizerVolume
import Theorems.Thm_GlobalTheory_HL_coset_fibre_card
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_T_orbit_mass_equivariant_constant_fibre
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL
namespace GlobalTheory.HL
theorem _root_.solution : ∀ {G : Type} [Group G] (Γ K0 : Subgroup G), ∃ V₀ : ℝ≥0∞, ∀ (X : Type) [MulAction G X] (x : X), K0.relIndex (MulAction.stabilizer G x) ≠ 0 → (MulAction.stabilizer G x).relIndex K0 ≠ 0 → (∑' o : MulAction.orbitRel.Quotient Γ X, if o.out ∈ MulAction.orbit G x then ((((Γ ⊓ MulAction.stabilizer G o.out : Subgroup G) : Set G).encard : ℝ≥0∞))⁻¹ else 0) = V₀ * ENNReal.ofReal (invVol K0 (MulAction.stabilizer G x)) := by
  intro G _ Γ K0
  let M : Subgroup G → ℝ≥0∞ := fun U => ∑' o : MulAction.orbitRel.Quotient Γ (G ⧸ U),
    ((((Γ ⊓ MulAction.stabilizer G o.out : Subgroup G) : Set G).encard : ℝ≥0∞))⁻¹
  have hq : ∀ (D H : Subgroup G) (h : D ≤ H), D.relIndex H ≠ 0 → M D = (D.relIndex H : ℝ≥0∞) * M H := by
    intro D H h hDH
    have e := GlobalTheory.T.orbit_mass_equivariant_constant_fibre Γ (G ⧸ D) (G ⧸ H) (Subgroup.quotientMapOfLE h) Set.univ (D.relIndex H) ?_
      (fun _ _ _ => trivial) (fun z _ => coset_fibre_card D H h hDH z) (fun z hz => absurd trivial hz)
    · simp only [Set.mem_univ, ite_true] at e
      exact e
    · intro g y
      induction y using QuotientGroup.induction_on with
      | H a => rfl
  refine ⟨M K0, fun X _ x h1 h2 => ?_⟩
  have hX : (∑' o : MulAction.orbitRel.Quotient Γ X, if o.out ∈ MulAction.orbit G x then
      ((((Γ ⊓ MulAction.stabilizer G o.out : Subgroup G) : Set G).encard : ℝ≥0∞))⁻¹ else 0) =
      M (MulAction.stabilizer G x) := by
    have e := GlobalTheory.T.orbit_mass_equivariant_constant_fibre Γ (G ⧸ MulAction.stabilizer G x) X (MulAction.ofQuotientStabilizer G x)
      (MulAction.orbit G x) 1 (fun g y => MulAction.ofQuotientStabilizer_smul G x g y)
      (fun g z hz => by obtain ⟨a, rfl⟩ := hz; exact ⟨g * a, mul_smul g a x⟩) ?_ ?_
    · rw [Nat.cast_one, one_mul] at e
      exact e.symm
    · intro z hz
      have hs : Subsingleton {y // MulAction.ofQuotientStabilizer G x y = z} :=
        ⟨fun a b => Subtype.ext (MulAction.injective_ofQuotientStabilizer G x (a.2.trans b.2.symm))⟩
      obtain ⟨a, rfl⟩ := hz
      have hn : Nonempty {y // MulAction.ofQuotientStabilizer G x y = a • x} :=
        ⟨⟨(a : G ⧸ MulAction.stabilizer G x), MulAction.ofQuotientStabilizer_mk G x a⟩⟩
      exact ⟨inferInstance, Nat.card_unique⟩
    · intro z hz
      refine ⟨fun y => hz ?_⟩
      rw [← y.2]
      induction y.1 using QuotientGroup.induction_on with
      | H a => exact ⟨a, (MulAction.ofQuotientStabilizer_mk G x a).symm⟩
  rw [hX]
  set U := MulAction.stabilizer G x
  have ha := hq (U ⊓ K0) U inf_le_left (by rw [Subgroup.inf_relIndex_left]; exact h1)
  have hb := hq (U ⊓ K0) K0 inf_le_right (by rw [Subgroup.inf_relIndex_right]; exact h2)
  rw [Subgroup.inf_relIndex_left] at ha
  rw [Subgroup.inf_relIndex_right] at hb
  rw [ha] at hb
  have hr : ENNReal.ofReal (invVol K0 U) = (U.relIndex K0 : ℝ≥0∞) / (K0.relIndex U : ℝ≥0∞) := by
    rw [invVol, ENNReal.ofReal_div_of_pos (by exact_mod_cast Nat.pos_of_ne_zero h1),
      ENNReal.ofReal_natCast, ENNReal.ofReal_natCast]
  have hA : (K0.relIndex U : ℝ≥0∞) ≠ 0 := by exact_mod_cast h1
  have hA' : (K0.relIndex U : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  rw [hr, ← mul_div_assoc, ENNReal.eq_div_iff hA hA', mul_comm (M K0), ← hb]
end GlobalTheory.HL
