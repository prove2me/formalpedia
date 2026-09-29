-- Prove2me | solution 1 for NumberField.PlaceDecomp.exists_conj_subgroupOf_and_transport_repHom_of_smul_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/29dea526-3ca6-5b87-a06a-3f7e070dcf03

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

namespace P2MW.S_NumberField_PlaceDecomp_exists_conj_subgroupOf_and_transport_repHom_of_smul_eq
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxSynthPendingDepth 3
p2m_open "CategoryTheory NumberField P2MW.S_NumberField_PlaceDecomp_exists_conj_subgroupOf_and_transport_repHom_of_smul_eq.NumberField IsDedekindDomain"
p2m_open_scoped "NumberField.PlaceDecomp P2MW.S_NumberField_PlaceDecomp_exists_conj_subgroupOf_and_transport_repHom_of_smul_eq.NumberField.PlaceDecomp NumberField.PlaceTransport"
open scoped Pointwise

namespace NumberField
p2m_export "NumberField" "PlaceDecomp.decomp PlaceDecomp.smul_def PlaceDecomp.coe_smul_units PlaceTransport.transport"
namespace PlaceDecomp
p2m_export "NumberField.PlaceDecomp" "decomp smul_def coe_smul_units"
namespace ConjSubgroupOfProof
p2m_open "NumberField.PlaceDecomp NumberField"

open NumberField.PlaceTransport
open scoped Pointwise

variable {E F : Type} [Field E] [Field F] [NumberField F] [Algebra E F]

theorem transport_congr {σ τ : F ≃ₐ[E] F} (hστ : σ = τ) {w w' : HeightOneSpectrum (𝓞 F)} (h : σ • w = w') (h' : τ • w = w') :
    transport σ h = transport τ h' := by
  subst hστ
  rfl

theorem mem_decomp_smul_iff (w : HeightOneSpectrum (𝓞 F)) (σ τ : F ≃ₐ[E] F) :
    τ ∈ decomp E F (σ • w) ↔ σ⁻¹ * τ * σ ∈ decomp E F w := by
  rw [← stabilizer_eq_decomp, ← stabilizer_eq_decomp, MulAction.mem_stabilizer_iff, MulAction.mem_stabilizer_iff,
    mul_smul, mul_smul, inv_smul_eq_iff]

variable (H : Subgroup (F ≃ₐ[E] F)) (w : HeightOneSpectrum (𝓞 F)) (σ : F ≃ₐ[E] F)

theorem mem_H (x : ↥((MulAut.conj σ • H).subgroupOf (decomp E F (σ • w)))) : σ⁻¹ * ((x : ↥(decomp E F (σ • w))) : F ≃ₐ[E] F) * σ ∈ H := by
  have hx := x.2
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_pointwise_smul_iff_inv_smul_mem, MulAut.smul_def, MulAut.conj_inv_apply] at hx
  exact hx

noncomputable def conjHom : ↥((MulAut.conj σ • H).subgroupOf (decomp E F (σ • w))) →* ↥(H ⊓ decomp E F w) where
  toFun x := ⟨σ⁻¹ * ((x : ↥(decomp E F (σ • w))) : F ≃ₐ[E] F) * σ,
    Subgroup.mem_inf.2 ⟨mem_H H w σ x, (mem_decomp_smul_iff w σ _).1 (x : ↥(decomp E F (σ • w))).2⟩⟩
  map_one' := Subtype.ext (by
    change σ⁻¹ * (((1 : ↥((MulAut.conj σ • H).subgroupOf (decomp E F (σ • w)))) : ↥(decomp E F (σ • w))) : F ≃ₐ[E] F) * σ = 1
    rw [Subgroup.coe_one, Subgroup.coe_one]; group)
  map_mul' a b := Subtype.ext (by
    change σ⁻¹ * (((a * b : ↥((MulAut.conj σ • H).subgroupOf (decomp E F (σ • w)))) : ↥(decomp E F (σ • w))) : F ≃ₐ[E] F) * σ =
      σ⁻¹ * ((a : ↥(decomp E F (σ • w))) : F ≃ₐ[E] F) * σ * (σ⁻¹ * ((b : ↥(decomp E F (σ • w))) : F ≃ₐ[E] F) * σ)
    rw [Subgroup.coe_mul, Subgroup.coe_mul]; group)

theorem coe_conjHom (x : ↥((MulAut.conj σ • H).subgroupOf (decomp E F (σ • w)))) :
    ((conjHom H w σ x : ↥(H ⊓ decomp E F w)) : F ≃ₐ[E] F) = σ⁻¹ * ((x : ↥(decomp E F (σ • w))) : F ≃ₐ[E] F) * σ := rfl

theorem conjHom_bijective : Function.Bijective (conjHom H w σ) := by
  constructor
  · intro a b h
    have h' := congrArg (fun t : ↥(H ⊓ decomp E F w) => (t : F ≃ₐ[E] F)) h
    simp only [coe_conjHom] at h'
    exact Subtype.ext (Subtype.ext (mul_left_cancel (mul_right_cancel h')))
  · intro y
    obtain ⟨hyH, hyD⟩ := Subgroup.mem_inf.1 y.2
    have hD : σ * (y : F ≃ₐ[E] F) * σ⁻¹ ∈ decomp E F (σ • w) := (mem_decomp_smul_iff w σ _).2 (by simpa [mul_assoc] using hyD)
    have hK : (⟨σ * (y : F ≃ₐ[E] F) * σ⁻¹, hD⟩ : ↥(decomp E F (σ • w))) ∈ (MulAut.conj σ • H).subgroupOf (decomp E F (σ • w)) := by
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_pointwise_smul_iff_inv_smul_mem, MulAut.smul_def, MulAut.conj_inv_apply]
      change σ⁻¹ * (σ * (y : F ≃ₐ[E] F) * σ⁻¹) * σ ∈ H
      simpa [mul_assoc] using hyH
    refine ⟨⟨_, hK⟩, Subtype.ext ?_⟩
    rw [coe_conjHom]
    change σ⁻¹ * (σ * (y : F ≃ₐ[E] F) * σ⁻¹) * σ = y
    group

theorem transport_smul (x : ↥((MulAut.conj σ • H).subgroupOf (decomp E F (σ • w)))) (y : w.adicCompletion F) :
    transport σ rfl ((Subgroup.inclusion (inf_le_right : H ⊓ decomp E F w ≤ decomp E F w) (conjHom H w σ x)) • y) =
      (x : ↥(decomp E F (σ • w))) • transport σ rfl y := by
  set τ : ↥(decomp E F (σ • w)) := (x : ↥(decomp E F (σ • w))) with hτdef
  set κ : ↥(decomp E F w) := Subgroup.inclusion (inf_le_right : H ⊓ decomp E F w ≤ decomp E F w) (conjHom H w σ x) with hκdef
  have hκ : ((κ : ↥(decomp E F w)) : F ≃ₐ[E] F) = σ⁻¹ * (τ : F ≃ₐ[E] F) * σ := rfl
  have hc : ((κ : ↥(decomp E F w)) : F ≃ₐ[E] F) • w = w :=
    MulAction.mem_stabilizer_iff.mp (((SetLike.ext_iff.mp (stabilizer_eq_decomp E F w)) _).2 κ.2)
  have hτ : ((τ : ↥(decomp E F (σ • w))) : F ≃ₐ[E] F) • (σ • w) = σ • w :=
    MulAction.mem_stabilizer_iff.mp (((SetLike.ext_iff.mp (stabilizer_eq_decomp E F (σ • w))) _).2 τ.2)
  have h₃ : (σ * ((κ : ↥(decomp E F w)) : F ≃ₐ[E] F)) • w = σ • w := by
    rw [hκ, show σ * (σ⁻¹ * (τ : F ≃ₐ[E] F) * σ) = (τ : F ≃ₐ[E] F) * σ by group, mul_smul, hτ]
  have h₃' : ((τ : F ≃ₐ[E] F) * σ) • w = σ • w := by rw [mul_smul, hτ]
  rw [NumberField.PlaceDecomp.smul_def, NumberField.PlaceDecomp.smul_def, ← transport_eq_actRingEquiv E F w κ hc,
    ← transport_eq_actRingEquiv E F (σ • w) τ hτ, ← RingEquiv.trans_apply, ← RingEquiv.trans_apply,
    transport_trans_transport E F σ _ hc rfl h₃, transport_trans_transport E F (τ : F ≃ₐ[E] F) σ rfl hτ h₃']
  exact congrFun (congrArg DFunLike.coe (transport_congr (by rw [hκ]; group) h₃ h₃')) y

noncomputable def T'' :
    Rep.res (conjHom H w σ) (Rep.res (Subgroup.inclusion (inf_le_right : H ⊓ decomp E F w ≤ decomp E F w))
        (Rep.ofMulDistribMulAction (↥(decomp E F w)) (w.adicCompletion F)ˣ)) ⟶
      Rep.res ((MulAut.conj σ • H).subgroupOf (decomp E F (σ • w))).subtype
        (Rep.ofMulDistribMulAction (↥(decomp E F (σ • w))) ((σ • w).adicCompletion F)ˣ) :=
  Rep.ofHom ⟨(MonoidHom.toAdditive (Units.map (transport σ (rfl : σ • w = σ • w)).toRingHom.toMonoidHom)).toIntLinearMap,
    fun x => LinearMap.ext fun a => by
      change Additive.ofMul (Units.map (transport σ (rfl : σ • w = σ • w)).toRingHom.toMonoidHom
          ((Subgroup.inclusion (inf_le_right : H ⊓ decomp E F w ≤ decomp E F w) (conjHom H w σ x)) • (Additive.toMul : _ ≃ (w.adicCompletion F)ˣ) a))
        = Additive.ofMul ((x : ↥(decomp E F (σ • w))) • Units.map (transport σ (rfl : σ • w = σ • w)).toRingHom.toMonoidHom ((Additive.toMul : _ ≃ (w.adicCompletion F)ˣ) a))
      congr 1
      apply Units.ext
      rw [NumberField.PlaceDecomp.coe_smul_units, Units.coe_map, Units.coe_map, NumberField.PlaceDecomp.coe_smul_units]
      exact transport_smul H w σ x _⟩

theorem T''_apply (u : (w.adicCompletion F)ˣ) :
    ((Additive.toMul ((T'' H w σ).hom (Additive.ofMul u)) : ((σ • w).adicCompletion F)ˣ) : (σ • w).adicCompletion F) = transport σ rfl (u : w.adicCompletion F) := rfl

end NumberField.PlaceDecomp.ConjSubgroupOfProof

theorem solution
    (E F : Type) [Field E] [Field F] [NumberField F] [Algebra E F] (H : Subgroup (F ≃ₐ[E] F))
    (w w₁ : HeightOneSpectrum (𝓞 F)) (g : F ≃ₐ[E] F) (hg : g • w₁ = w) :
    Nat.card ↥((MulAut.conj g • H).subgroupOf (NumberField.PlaceDecomp.decomp E F w)) = Nat.card ↥(H ⊓ (NumberField.PlaceDecomp.decomp E F w₁)) ∧
    ∃ (c'' : ↥((MulAut.conj g • H).subgroupOf (NumberField.PlaceDecomp.decomp E F w)) →* ↥(H ⊓ (NumberField.PlaceDecomp.decomp E F w₁)))
      (T'' : Rep.res c'' (Rep.res (Subgroup.inclusion (inf_le_right : H ⊓ (NumberField.PlaceDecomp.decomp E F w₁) ≤ (NumberField.PlaceDecomp.decomp E F w₁)))
          (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w₁)) (w₁.adicCompletion F)ˣ)) ⟶
        Rep.res ((MulAut.conj g • H).subgroupOf (NumberField.PlaceDecomp.decomp E F w)).subtype
          (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (w.adicCompletion F)ˣ)),
      Function.Bijective c'' ∧
      (∀ x : ↥((MulAut.conj g • H).subgroupOf (NumberField.PlaceDecomp.decomp E F w)),
        ((c'' x : ↥(H ⊓ (NumberField.PlaceDecomp.decomp E F w₁))) : F ≃ₐ[E] F) = g⁻¹ * ((x : ↥(NumberField.PlaceDecomp.decomp E F w)) : F ≃ₐ[E] F) * g) ∧
      (∀ x : (w₁.adicCompletion F)ˣ, ((Additive.toMul (T''.hom (Additive.ofMul x)) : (w.adicCompletion F)ˣ) : w.adicCompletion F) =
        NumberField.PlaceTransport.transport g hg (x : w₁.adicCompletion F)) := by
  subst hg
  refine ⟨Nat.card_eq_of_bijective _ (NumberField.PlaceDecomp.ConjSubgroupOfProof.conjHom_bijective H w₁ g),
    NumberField.PlaceDecomp.ConjSubgroupOfProof.conjHom H w₁ g, NumberField.PlaceDecomp.ConjSubgroupOfProof.T'' H w₁ g,
    NumberField.PlaceDecomp.ConjSubgroupOfProof.conjHom_bijective H w₁ g, fun x => rfl, fun x => rfl⟩

end S_NumberField_PlaceDecomp_exists_conj_subgroupOf_and_transport_repHom_of_smul_eq
end P2MW
export P2MW.S_NumberField_PlaceDecomp_exists_conj_subgroupOf_and_transport_repHom_of_smul_eq (solution)
