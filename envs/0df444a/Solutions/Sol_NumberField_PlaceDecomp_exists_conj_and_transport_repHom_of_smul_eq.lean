-- Prove2me | solution 1 for NumberField.PlaceDecomp.exists_conj_and_transport_repHom_of_smul_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/9bf455e1-3d9e-5282-8feb-e10ce862914c

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

namespace P2MW.S_NumberField_PlaceDecomp_exists_conj_and_transport_repHom_of_smul_eq
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxSynthPendingDepth 3
p2m_open "CategoryTheory NumberField P2MW.S_NumberField_PlaceDecomp_exists_conj_and_transport_repHom_of_smul_eq.NumberField IsDedekindDomain"
p2m_open_scoped "NumberField.PlaceDecomp P2MW.S_NumberField_PlaceDecomp_exists_conj_and_transport_repHom_of_smul_eq.NumberField.PlaceDecomp NumberField.PlaceTransport"

namespace NumberField
p2m_export "NumberField" "place PlaceDecomp.decomp PlaceDecomp.smul_def PlaceDecomp.coe_smul_units PlaceTransport.transport PlaceTransport.transport_eq_actRingEquiv PlaceTransport.transport_trans_transport"
namespace PlaceDecomp
p2m_export "NumberField.PlaceDecomp" "decomp smul_def coe_smul_units"
namespace ConjDataProof
p2m_open "NumberField.PlaceDecomp NumberField"

open NumberField.PlaceTransport

noncomputable def resRepHom {G H : Type} [Group G] [Group H] (φ : H →* G) {M N : Type} [CommGroup M] [CommGroup N]
    [MulDistribMulAction G M] [MulDistribMulAction H N] (f : M →* N) (hf : ∀ (h : H) (m : M), f (φ h • m) = h • f m) :
    Rep.res φ (Rep.ofMulDistribMulAction G M) ⟶ Rep.ofMulDistribMulAction H N :=
  Rep.ofHom ⟨(MonoidHom.toAdditive f).toIntLinearMap, fun h => LinearMap.ext fun a => by
    change Additive.ofMul (f (φ h • (Additive.toMul : _ ≃ M) a)) = Additive.ofMul (h • f ((Additive.toMul : _ ≃ M) a))
    rw [hf]⟩

variable {E F : Type} [Field E] [Field F] [NumberField F] [Algebra E F]

theorem transport_congr {σ τ : F ≃ₐ[E] F} (hστ : σ = τ) {w w' : HeightOneSpectrum (𝓞 F)} (h : σ • w = w') (h' : τ • w = w') :
    transport σ h = transport τ h' := by
  subst hστ
  rfl

theorem mem_decomp_smul_iff (w : HeightOneSpectrum (𝓞 F)) (σ τ : F ≃ₐ[E] F) :
    τ ∈ decomp E F (σ • w) ↔ σ⁻¹ * τ * σ ∈ decomp E F w := by
  rw [← stabilizer_eq_decomp, ← stabilizer_eq_decomp, MulAction.mem_stabilizer_iff, MulAction.mem_stabilizer_iff,
    mul_smul, mul_smul, inv_smul_eq_iff]

noncomputable def conjHom (w : HeightOneSpectrum (𝓞 F)) (σ : F ≃ₐ[E] F) : ↥(decomp E F (σ • w)) →* ↥(decomp E F w) where
  toFun τ := ⟨σ⁻¹ * (τ : F ≃ₐ[E] F) * σ, (mem_decomp_smul_iff w σ τ).1 τ.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' a b := Subtype.ext (by
    change σ⁻¹ * ((a : F ≃ₐ[E] F) * b) * σ = σ⁻¹ * (a : F ≃ₐ[E] F) * σ * (σ⁻¹ * (b : F ≃ₐ[E] F) * σ)
    group)

theorem coe_conjHom (w : HeightOneSpectrum (𝓞 F)) (σ : F ≃ₐ[E] F) (τ : ↥(decomp E F (σ • w))) :
    ((conjHom w σ τ : ↥(decomp E F w)) : F ≃ₐ[E] F) = σ⁻¹ * (τ : F ≃ₐ[E] F) * σ := rfl

theorem conjHom_bijective (w : HeightOneSpectrum (𝓞 F)) (σ : F ≃ₐ[E] F) : Function.Bijective (conjHom w σ) := by
  constructor
  · intro a b h
    have h' := congrArg (fun t : ↥(decomp E F w) => (t : F ≃ₐ[E] F)) h
    simp only [coe_conjHom] at h'
    exact Subtype.ext (mul_left_cancel (mul_right_cancel h'))
  · intro g
    refine ⟨⟨σ * (g : F ≃ₐ[E] F) * σ⁻¹, (mem_decomp_smul_iff w σ _).2 (by simpa [mul_assoc] using g.2)⟩, Subtype.ext ?_⟩
    rw [coe_conjHom]
    group

theorem transport_smul (w : HeightOneSpectrum (𝓞 F)) (σ : F ≃ₐ[E] F) (τ : ↥(decomp E F (σ • w))) (y : w.adicCompletion F) :
    transport σ rfl ((conjHom w σ τ) • y) = τ • transport σ rfl y := by
  have hc : ((conjHom w σ τ : ↥(decomp E F w)) : F ≃ₐ[E] F) • w = w :=
    MulAction.mem_stabilizer_iff.mp (((SetLike.ext_iff.mp (stabilizer_eq_decomp E F w)) _).2 (conjHom w σ τ).2)
  have hτ : ((τ : ↥(decomp E F (σ • w))) : F ≃ₐ[E] F) • (σ • w) = σ • w :=
    MulAction.mem_stabilizer_iff.mp (((SetLike.ext_iff.mp (stabilizer_eq_decomp E F (σ • w))) _).2 τ.2)
  have h₃ : (σ * (σ⁻¹ * (τ : F ≃ₐ[E] F) * σ)) • w = σ • w := by
    rw [show σ * (σ⁻¹ * (τ : F ≃ₐ[E] F) * σ) = (τ : F ≃ₐ[E] F) * σ by group, mul_smul, hτ]
  have h₃' : ((τ : F ≃ₐ[E] F) * σ) • w = σ • w := by rw [mul_smul, hτ]
  rw [NumberField.PlaceDecomp.smul_def, NumberField.PlaceDecomp.smul_def, ← transport_eq_actRingEquiv E F w (conjHom w σ τ) hc,
    ← transport_eq_actRingEquiv E F (σ • w) τ hτ, ← RingEquiv.trans_apply, ← RingEquiv.trans_apply,
    transport_trans_transport E F σ _ hc rfl h₃, transport_trans_transport E F (τ : F ≃ₐ[E] F) σ rfl hτ h₃']
  exact congrFun (congrArg DFunLike.coe (transport_congr (by group) h₃ h₃')) y

end NumberField.PlaceDecomp.ConjDataProof

open _root_.NumberField.PlaceDecomp _root_.P2MW.S_NumberField_PlaceDecomp_exists_conj_and_transport_repHom_of_smul_eq.NumberField.PlaceDecomp NumberField.PlaceDecomp.ConjDataProof NumberField.PlaceTransport in

theorem solution
    (E F : Type) [Field E] [Field F] [NumberField F] [Algebra E F]
    (w w₁ : HeightOneSpectrum (𝓞 F)) (σ : F ≃ₐ[E] F) (hσ : σ • w = w₁) :
    Nat.card ↥(NumberField.PlaceDecomp.decomp E F w₁) = Nat.card ↥(NumberField.PlaceDecomp.decomp E F w) ∧
    ∃ (c : ↥(NumberField.PlaceDecomp.decomp E F w₁) →* ↥(NumberField.PlaceDecomp.decomp E F w))
      (T : Rep.res c (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (w.adicCompletion F)ˣ) ⟶
        Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w₁)) (w₁.adicCompletion F)ˣ),
      Function.Bijective c ∧
      (∀ τ : ↥(NumberField.PlaceDecomp.decomp E F w₁), ((c τ : ↥(NumberField.PlaceDecomp.decomp E F w)) : F ≃ₐ[E] F) = σ⁻¹ * (τ : F ≃ₐ[E] F) * σ) ∧
      (∀ x : (w.adicCompletion F)ˣ, ((Additive.toMul (T.hom (Additive.ofMul x)) : (w₁.adicCompletion F)ˣ) : w₁.adicCompletion F) =
        NumberField.PlaceTransport.transport σ hσ (x : w.adicCompletion F)) := by
  subst hσ
  refine ⟨Nat.card_eq_of_bijective _ (conjHom_bijective w σ), conjHom w σ,
    resRepHom (conjHom w σ) (Units.map (transport σ (rfl : σ • w = σ • w)).toRingHom.toMonoidHom) (fun τ x => Units.ext ?_),
    conjHom_bijective w σ, coe_conjHom w σ, fun x => rfl⟩
  rw [NumberField.PlaceDecomp.coe_smul_units, Units.coe_map, Units.coe_map, NumberField.PlaceDecomp.coe_smul_units]
  exact transport_smul w σ τ (x : w.adicCompletion F)

end S_NumberField_PlaceDecomp_exists_conj_and_transport_repHom_of_smul_eq
end P2MW
export P2MW.S_NumberField_PlaceDecomp_exists_conj_and_transport_repHom_of_smul_eq (solution)
