-- Prove2me | solution 1 for NumberField.PlaceDecomp.exists_conj_and_transport_repHom_inf_decomp_of_smul_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/db48b2af-7a0a-572b-9d90-6b8c088f33f3

import Mathlib
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_NumberField_PlaceTransport
import Theorems.Thm_NumberField_PlaceTransport_transport_eq_actRingEquiv
import Theorems.Thm_NumberField_PlaceTransport_transport_trans_transport
import Theorems.Thm_NumberField_PlaceTransport_stabilizer_eq_decomp
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_PlaceDecomp_exists_conj_and_transport_repHom_inf_decomp_of_smul_eq
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxSynthPendingDepth 3
p2m_open "CategoryTheory NumberField P2MW.S_NumberField_PlaceDecomp_exists_conj_and_transport_repHom_inf_decomp_of_smul_eq.NumberField IsDedekindDomain"
p2m_open_scoped "NumberField.PlaceDecomp P2MW.S_NumberField_PlaceDecomp_exists_conj_and_transport_repHom_inf_decomp_of_smul_eq.NumberField.PlaceDecomp NumberField.PlaceTransport"

namespace NumberField
p2m_export "NumberField" "place PlaceDecomp.decomp PlaceDecomp.smul_def PlaceDecomp.coe_smul_units PlaceTransport.transport PlaceTransport.stabilizer_eq_decomp"
namespace PlaceDecomp
p2m_export "NumberField.PlaceDecomp" "decomp smul_def coe_smul_units"
namespace ConjDataHProof
p2m_open "NumberField.PlaceDecomp NumberField"

open NumberField.PlaceTransport

variable {E F : Type} [Field E] [Field F] [NumberField F] [Algebra E F]

theorem transport_congr {σ τ : F ≃ₐ[E] F} (hστ : σ = τ) {w w' : HeightOneSpectrum (𝓞 F)} (h : σ • w = w') (h' : τ • w = w') :
    transport σ h = transport τ h' := by
  subst hστ
  rfl

theorem mem_decomp_smul_iff (w : HeightOneSpectrum (𝓞 F)) (σ τ : F ≃ₐ[E] F) :
    τ ∈ decomp E F (σ • w) ↔ σ⁻¹ * τ * σ ∈ decomp E F w := by
  rw [← stabilizer_eq_decomp, ← stabilizer_eq_decomp, MulAction.mem_stabilizer_iff, MulAction.mem_stabilizer_iff,
    mul_smul, mul_smul, inv_smul_eq_iff]

theorem transport_smul (w : HeightOneSpectrum (𝓞 F)) (σ : F ≃ₐ[E] F) (τ : ↥(decomp E F (σ • w)))
    (g : ↥(decomp E F w)) (hg : (g : F ≃ₐ[E] F) = σ⁻¹ * (τ : F ≃ₐ[E] F) * σ) (y : w.adicCompletion F) :
    transport σ rfl (g • y) = τ • transport σ rfl y := by
  have hc : ((g : ↥(decomp E F w)) : F ≃ₐ[E] F) • w = w :=
    MulAction.mem_stabilizer_iff.mp (((SetLike.ext_iff.mp (stabilizer_eq_decomp E F w)) _).2 g.2)
  have hτ : ((τ : ↥(decomp E F (σ • w))) : F ≃ₐ[E] F) • (σ • w) = σ • w :=
    MulAction.mem_stabilizer_iff.mp (((SetLike.ext_iff.mp (stabilizer_eq_decomp E F (σ • w))) _).2 τ.2)
  have h₃ : (σ * (g : F ≃ₐ[E] F)) • w = σ • w := by
    rw [hg, show σ * (σ⁻¹ * (τ : F ≃ₐ[E] F) * σ) = (τ : F ≃ₐ[E] F) * σ by group, mul_smul, hτ]
  have h₃' : ((τ : F ≃ₐ[E] F) * σ) • w = σ • w := by rw [mul_smul, hτ]
  rw [NumberField.PlaceDecomp.smul_def, NumberField.PlaceDecomp.smul_def, ← transport_eq_actRingEquiv E F w g hc,
    ← transport_eq_actRingEquiv E F (σ • w) τ hτ, ← RingEquiv.trans_apply, ← RingEquiv.trans_apply,
    transport_trans_transport E F σ _ hc rfl h₃, transport_trans_transport E F (τ : F ≃ₐ[E] F) σ rfl hτ h₃']
  exact congrFun (congrArg DFunLike.coe (transport_congr (by rw [hg]; group) h₃ h₃')) y

variable (H : Subgroup (F ≃ₐ[E] F))

theorem mem_inf_decomp_smul_iff (w : HeightOneSpectrum (𝓞 F)) (h : ↥H) (x : F ≃ₐ[E] F) :
    x ∈ H ⊓ (decomp E F ((h : F ≃ₐ[E] F) • w)) ↔ (h : F ≃ₐ[E] F)⁻¹ * x * h ∈ H ⊓ (decomp E F w) := by
  rw [Subgroup.mem_inf, Subgroup.mem_inf, mem_decomp_smul_iff]
  refine and_congr_left fun _ => ⟨fun hx => H.mul_mem (H.mul_mem (H.inv_mem h.2) hx) h.2, fun hx => ?_⟩
  have := H.mul_mem (H.mul_mem h.2 hx) (H.inv_mem h.2)
  simpa [mul_assoc] using this

noncomputable def conjHomH (w : HeightOneSpectrum (𝓞 F)) (h : ↥H) : ↥(H ⊓ (decomp E F ((h : F ≃ₐ[E] F) • w))) →* ↥(H ⊓ (decomp E F w)) where
  toFun x := ⟨(h : F ≃ₐ[E] F)⁻¹ * (x : F ≃ₐ[E] F) * h, (mem_inf_decomp_smul_iff H w h x).1 x.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' a b := Subtype.ext (by
    change (h : F ≃ₐ[E] F)⁻¹ * ((a : F ≃ₐ[E] F) * b) * h = (h : F ≃ₐ[E] F)⁻¹ * (a : F ≃ₐ[E] F) * h * ((h : F ≃ₐ[E] F)⁻¹ * (b : F ≃ₐ[E] F) * h)
    group)

theorem coe_conjHomH (w : HeightOneSpectrum (𝓞 F)) (h : ↥H) (x : ↥(H ⊓ (decomp E F ((h : F ≃ₐ[E] F) • w)))) :
    ((conjHomH H w h x : ↥(H ⊓ (decomp E F w))) : F ≃ₐ[E] F) = (h : F ≃ₐ[E] F)⁻¹ * (x : F ≃ₐ[E] F) * h := rfl

theorem conjHomH_bijective (w : HeightOneSpectrum (𝓞 F)) (h : ↥H) : Function.Bijective (conjHomH H w h) := by
  constructor
  · intro a b hab
    have h' := congrArg (fun t : ↥(H ⊓ (decomp E F w)) => (t : F ≃ₐ[E] F)) hab
    simp only [coe_conjHomH] at h'
    exact Subtype.ext (mul_left_cancel (mul_right_cancel h'))
  · intro y
    refine ⟨⟨(h : F ≃ₐ[E] F) * (y : F ≃ₐ[E] F) * (h : F ≃ₐ[E] F)⁻¹, (mem_inf_decomp_smul_iff H w h _).2 (by simpa [mul_assoc] using y.2)⟩,
      Subtype.ext ?_⟩
    rw [coe_conjHomH]
    group

end NumberField.PlaceDecomp.ConjDataHProof

open _root_.NumberField.PlaceDecomp _root_.P2MW.S_NumberField_PlaceDecomp_exists_conj_and_transport_repHom_inf_decomp_of_smul_eq.NumberField.PlaceDecomp NumberField.PlaceDecomp.ConjDataHProof NumberField.PlaceTransport in

theorem solution
    (E F : Type) [Field E] [Field F] [NumberField F] [Algebra E F] (H : Subgroup (F ≃ₐ[E] F))
    (w w₁ : HeightOneSpectrum (𝓞 F)) (h : ↥H) (hh : (h : F ≃ₐ[E] F) • w = w₁) :
    Nat.card ↥(H ⊓ (NumberField.PlaceDecomp.decomp E F w₁)) = Nat.card ↥(H ⊓ (NumberField.PlaceDecomp.decomp E F w)) ∧
    ∃ (ch : ↥(H ⊓ (NumberField.PlaceDecomp.decomp E F w₁)) →* ↥(H ⊓ (NumberField.PlaceDecomp.decomp E F w)))
      (Th : Rep.res ch (Rep.res (Subgroup.inclusion (inf_le_right : H ⊓ (NumberField.PlaceDecomp.decomp E F w) ≤ (NumberField.PlaceDecomp.decomp E F w)))
          (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (w.adicCompletion F)ˣ)) ⟶
        Rep.res (Subgroup.inclusion (inf_le_right : H ⊓ (NumberField.PlaceDecomp.decomp E F w₁) ≤ (NumberField.PlaceDecomp.decomp E F w₁)))
          (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w₁)) (w₁.adicCompletion F)ˣ)),
      Function.Bijective ch ∧
      (∀ x : ↥(H ⊓ (NumberField.PlaceDecomp.decomp E F w₁)),
        ((ch x : ↥(H ⊓ (NumberField.PlaceDecomp.decomp E F w))) : F ≃ₐ[E] F) = (h : F ≃ₐ[E] F)⁻¹ * (x : F ≃ₐ[E] F) * (h : F ≃ₐ[E] F)) ∧
      (∀ x : (w.adicCompletion F)ˣ, ((Additive.toMul (Th.hom (Additive.ofMul x)) : (w₁.adicCompletion F)ˣ) : w₁.adicCompletion F) =
        NumberField.PlaceTransport.transport (h : F ≃ₐ[E] F) hh (x : w.adicCompletion F)) := by
  subst hh
  refine ⟨Nat.card_eq_of_bijective _ (conjHomH_bijective H w h), conjHomH H w h,
    Rep.ofHom ⟨(MonoidHom.toAdditive (Units.map (transport (h : F ≃ₐ[E] F) (rfl : (h : F ≃ₐ[E] F) • w = (h : F ≃ₐ[E] F) • w)).toRingHom.toMonoidHom)).toIntLinearMap,
      fun x => LinearMap.ext fun a => ?_⟩,
    conjHomH_bijective H w h, coe_conjHomH H w h, fun x => rfl⟩
  change Additive.ofMul (Units.map (transport (h : F ≃ₐ[E] F) rfl).toRingHom.toMonoidHom
      ((Subgroup.inclusion (inf_le_right : H ⊓ (decomp E F w) ≤ (decomp E F w)) (conjHomH H w h x)) • (Additive.toMul : _ ≃ (w.adicCompletion F)ˣ) a))
    = Additive.ofMul ((Subgroup.inclusion (inf_le_right : H ⊓ (decomp E F ((h : F ≃ₐ[E] F) • w)) ≤ (decomp E F ((h : F ≃ₐ[E] F) • w))) x) •
        Units.map (transport (h : F ≃ₐ[E] F) rfl).toRingHom.toMonoidHom ((Additive.toMul : _ ≃ (w.adicCompletion F)ˣ) a))
  congr 1
  apply Units.ext
  rw [NumberField.PlaceDecomp.coe_smul_units, Units.coe_map, Units.coe_map, NumberField.PlaceDecomp.coe_smul_units]
  exact transport_smul w (h : F ≃ₐ[E] F) (Subgroup.inclusion inf_le_right x) (Subgroup.inclusion inf_le_right (conjHomH H w h x)) rfl _

end S_NumberField_PlaceDecomp_exists_conj_and_transport_repHom_inf_decomp_of_smul_eq
end P2MW
export P2MW.S_NumberField_PlaceDecomp_exists_conj_and_transport_repHom_inf_decomp_of_smul_eq (solution)
