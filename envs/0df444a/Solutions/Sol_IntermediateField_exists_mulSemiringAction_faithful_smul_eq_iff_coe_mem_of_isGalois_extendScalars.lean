-- Prove2me | solution 1 for IntermediateField.exists_mulSemiringAction_faithful_smul_eq_iff_coe_mem_of_isGalois_extendScalars
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/8ac7774f-5ac3-55ba-a1cf-0ba22861ae5a

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IntermediateField_exists_mulSemiringAction_faithful_smul_eq_iff_coe_mem_of_isGalois_extendScalars

set_option autoImplicit false

universe u v

theorem solution
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L] (F E : IntermediateField K L) (hle : F ≤ E)
    [FiniteDimensional ↥F ↥(IntermediateField.extendScalars hle)]
    [IsGalois ↥F ↥(IntermediateField.extendScalars hle)] :
    ∃ (G : Type v) (_ : Group G) (_ : Fintype G) (_ : MulSemiringAction G ↥E),
      FaithfulSMul G ↥E ∧
      (∀ (g : G) (x : ↥E), (x : L) ∈ F → g • x = x) ∧
      (∀ x : ↥E, (∀ g : G, g • x = x) → (x : L) ∈ F) := by
  classical
  set E' := IntermediateField.extendScalars hle with hE'

  let eKE : ↥E ≃+* ↥E' :=
    { toFun := fun x => ⟨(x : L), (IntermediateField.mem_extendScalars hle).mpr x.2⟩
      invFun := fun x => ⟨(x : L), (IntermediateField.mem_extendScalars hle).mp x.2⟩
      left_inv := fun x => rfl
      right_inv := fun x => rfl
      map_mul' := fun x y => rfl
      map_add' := fun x y => rfl }
  have heKE : ∀ x : ↥E, ((eKE x : ↥E') : L) = (x : L) := fun _ => rfl
  have heKE' : ∀ x : ↥E', ((eKE.symm x : ↥E) : L) = (x : L) := fun _ => rfl
  let G := ↥E' ≃ₐ[↥F] ↥E'

  let φ : G →* (↥E ≃+* ↥E) :=
    { toFun := fun g => (eKE.trans (g : ↥E' ≃+* ↥E')).trans eKE.symm
      map_one' := by
        ext x
        rfl
      map_mul' := fun g h => by
        ext x
        rfl }
  letI act : MulSemiringAction G ↥E := MulSemiringAction.compHom ↥E φ
  have hact : ∀ (g : G) (x : ↥E), ((g • x : ↥E) : L) = ((g (eKE x) : ↥E') : L) := fun g x => rfl
  refine ⟨G, inferInstance, AlgEquiv.fintype ↥F ↥E', act, ?_, ?_, ?_⟩
  ·
    refine ⟨fun {g h} hgh => AlgEquiv.ext fun e => ?_⟩
    have := hgh (eKE.symm e)
    apply Subtype.ext
    have h1 := congrArg Subtype.val this
    rw [hact, hact, RingEquiv.apply_symm_apply] at h1
    exact h1
  ·
    intro g x hx
    apply Subtype.ext
    rw [hact]
    have hc := g.commutes ⟨(x : L), hx⟩
    have : algebraMap ↥F ↥E' ⟨(x : L), hx⟩ = eKE x := Subtype.ext rfl
    rw [this] at hc
    rw [hc]
    exact heKE x
  ·
    intro x hx
    have hmem : eKE x ∈ IntermediateField.fixedField (⊤ : Subgroup G) := by
      rw [IntermediateField.mem_fixedField_iff]
      intro g _
      apply Subtype.ext
      have := congrArg Subtype.val (hx g)
      rw [hact] at this
      exact this
    have htfae := IsGalois.tfae (F := ↥F) (E := ↥E')
    have htop : IntermediateField.fixedField (⊤ : Subgroup G) = ⊥ := (htfae.out 0 1).mp ‹IsGalois ↥F ↥E'›
    rw [htop, IntermediateField.mem_bot] at hmem
    obtain ⟨c, hc⟩ := hmem
    have : (x : L) = ((c : ↥F) : L) := by
      have h1 := congrArg Subtype.val hc
      rw [heKE] at h1
      exact h1.symm
    rw [this]
    exact c.2

end S_IntermediateField_exists_mulSemiringAction_faithful_smul_eq_iff_coe_mem_of_isGalois_extendScalars
end P2MW
export P2MW.S_IntermediateField_exists_mulSemiringAction_faithful_smul_eq_iff_coe_mem_of_isGalois_extendScalars (solution)
