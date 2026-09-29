-- Prove2me | solution 1 for NumberField.PlaceTransport.exists_bijective_doubleCoset_decomp_of_under_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/650ee14b-dd1c-5f08-9572-941e95a6db16

import Mathlib
import Definitions.Def_NumberField_PlaceTransport
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_NumberField_PlaceAbove
import Theorems.Thm_NumberField_PlaceTransport_orbit_eq_setOf_under_eq
import Theorems.Thm_NumberField_PlaceTransport_stabilizer_eq_decomp
import Theorems.Thm_NumberField_PlaceTransport_under_smul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_PlaceTransport_exists_bijective_doubleCoset_decomp_of_under_eq

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
p2m_open "IsDedekindDomain NumberField P2MW.S_NumberField_PlaceTransport_exists_bijective_doubleCoset_decomp_of_under_eq.NumberField"
p2m_open_scoped "NumberField.PlaceTransport P2MW.S_NumberField_PlaceTransport_exists_bijective_doubleCoset_decomp_of_under_eq.NumberField.PlaceTransport Pointwise"

namespace NumberField
p2m_export "NumberField" "mk place PlaceTransport.mem_smul_asIdeal_iff PlaceDecomp.decomp PlaceAbove.above PlaceAbove.comap_above PlaceTransport.orbit_eq_setOf_under_eq PlaceTransport.stabilizer_eq_decomp PlaceTransport.under_smul"
namespace PlaceTransport
p2m_export "NumberField.PlaceTransport" "mem_smul_asIdeal_iff transport orbit_eq_setOf_under_eq stabilizer_eq_decomp under_smul"
namespace Dict
p2m_open "NumberField.PlaceTransport NumberField"

p2m_open_scoped "NumberField.PlaceTransport P2MW.S_NumberField_PlaceTransport_exists_bijective_doubleCoset_decomp_of_under_eq.NumberField.PlaceTransport Pointwise"

variable {E F : Type} [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F]

section overK
variable (K : IntermediateField E F)

theorem smul_eq_smul_of_forall_apply_eq (σ : F ≃ₐ[E] F) (σ' : F ≃ₐ[K] F) (h : ∀ x, σ x = σ' x)
    (w : HeightOneSpectrum (𝓞 F)) : σ • w = σ' • w := by
  have hsymm : ∀ x, σ.symm x = σ'.symm x := fun x => by
    apply σ'.injective
    rw [AlgEquiv.apply_symm_apply, ← h, AlgEquiv.apply_symm_apply]
  apply HeightOneSpectrum.ext
  apply Ideal.ext
  intro x
  rw [NumberField.PlaceTransport.mem_smul_asIdeal_iff, NumberField.PlaceTransport.mem_smul_asIdeal_iff]
  have hx : (σ⁻¹ • x : 𝓞 F) = (σ'⁻¹ • x : 𝓞 F) := by
    apply Subtype.ext
    change σ⁻¹ (x : F) = σ'⁻¹ (x : F)
    exact hsymm x
  rw [hx]

noncomputable def toAlgEquivOver (σ : F ≃ₐ[E] F) (hσ : ∀ x : K, σ x = x) : F ≃ₐ[K] F :=
  AlgEquiv.ofRingEquiv (f := σ.toRingEquiv) (fun x => hσ x)

theorem toAlgEquivOver_apply (σ : F ≃ₐ[E] F) (hσ : ∀ x : K, σ x = x) (y : F) : toAlgEquivOver K σ hσ y = σ y := rfl

theorem under_smul_of_forall_apply_eq (σ : F ≃ₐ[E] F) (hσ : ∀ x : K, σ x = x) (w : HeightOneSpectrum (𝓞 F)) :
    (σ • w).under (𝓞 K) = w.under (𝓞 K) := by
  rw [smul_eq_smul_of_forall_apply_eq K σ (toAlgEquivOver K σ hσ) (fun x => rfl) w]
  exact NumberField.PlaceTransport.under_smul K F (toAlgEquivOver K σ hσ) w

theorem exists_smul_eq_of_under_eq [IsGalois K F] (w₁ w₂ : HeightOneSpectrum (𝓞 F)) (h : w₁.under (𝓞 K) = w₂.under (𝓞 K)) :
    ∃ σ : F ≃ₐ[E] F, (∀ x : K, σ x = x) ∧ σ • w₁ = w₂ := by
  have hmem : w₂ ∈ MulAction.orbit (F ≃ₐ[K] F) w₁ := by
    rw [NumberField.PlaceTransport.orbit_eq_setOf_under_eq K F w₁]
    exact h.symm
  obtain ⟨σ', hσ'⟩ := hmem
  refine ⟨σ'.restrictScalars E, fun x => σ'.commutes x, ?_⟩
  rw [smul_eq_smul_of_forall_apply_eq K (σ'.restrictScalars E) σ' (fun x => rfl) w₁]
  exact hσ'

private theorem _root_.NumberField.PlaceTransport.Dict.under_under (w : HeightOneSpectrum (𝓞 F)) : (w.under (𝓞 K)).under (𝓞 E) = w.under (𝓞 E) := by
  apply HeightOneSpectrum.ext
  change (w.asIdeal.under (𝓞 K)).under (𝓞 E) = w.asIdeal.under (𝓞 E)
  rw [Ideal.under_under]

p2m_export "NumberField.PlaceTransport.Dict" "under_under"
end overK

section fixedField
variable (H : Subgroup (F ≃ₐ[E] F))

theorem apply_eq_of_mem {h : F ≃ₐ[E] F} (hh : h ∈ H) (x : ↥(IntermediateField.fixedField H)) : h x = x :=
  (IntermediateField.mem_fixedField_iff H (x : F)).1 x.2 h hh

variable [IsGalois E F]

theorem mem_of_forall_apply_eq {h : F ≃ₐ[E] F} (hh : ∀ x : ↥(IntermediateField.fixedField H), h x = x) : h ∈ H := by
  rw [← IntermediateField.fixingSubgroup_fixedField H]
  exact fun x => hh x

theorem under_smul_of_mem {h : F ≃ₐ[E] F} (hh : h ∈ H) (w : HeightOneSpectrum (𝓞 F)) :
    (h • w).under (𝓞 ↥(IntermediateField.fixedField H)) = w.under (𝓞 ↥(IntermediateField.fixedField H)) :=
  under_smul_of_forall_apply_eq (IntermediateField.fixedField H) h (apply_eq_of_mem H hh) w

theorem exists_mem_smul_eq_of_under_eq (w₁ w₂ : HeightOneSpectrum (𝓞 F))
    (h : w₁.under (𝓞 ↥(IntermediateField.fixedField H)) = w₂.under (𝓞 ↥(IntermediateField.fixedField H))) :
    ∃ g : ↥H, (g : F ≃ₐ[E] F) • w₁ = w₂ := by
  obtain ⟨σ, hσ, hw⟩ := exists_smul_eq_of_under_eq (IntermediateField.fixedField H) w₁ w₂ h
  exact ⟨⟨σ, mem_of_forall_apply_eq H hσ⟩, hw⟩

end fixedField

theorem mem_decomp_iff (σ : F ≃ₐ[E] F) (w : HeightOneSpectrum (𝓞 F)) : σ ∈ NumberField.PlaceDecomp.decomp E F w ↔ σ • w = w := by
  rw [← NumberField.PlaceTransport.stabilizer_eq_decomp E F w, MulAction.mem_stabilizer_iff]

end NumberField.PlaceTransport.Dict

namespace NumberField
p2m_export "NumberField" "mk place PlaceTransport.mem_smul_asIdeal_iff PlaceDecomp.decomp PlaceAbove.above PlaceAbove.comap_above PlaceTransport.orbit_eq_setOf_under_eq PlaceTransport.stabilizer_eq_decomp PlaceTransport.under_smul"
namespace PlaceTransport
p2m_export "NumberField.PlaceTransport" "mem_smul_asIdeal_iff transport orbit_eq_setOf_under_eq stabilizer_eq_decomp under_smul"
namespace Dict
p2m_open "NumberField.PlaceTransport NumberField"

p2m_open_scoped "NumberField.PlaceTransport P2MW.S_NumberField_PlaceTransport_exists_bijective_doubleCoset_decomp_of_under_eq.NumberField.PlaceTransport Pointwise"

variable {E F : Type} [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F] [IsGalois E F]

theorem under_above (K : IntermediateField E F) (v' : HeightOneSpectrum (𝓞 K)) :
    (NumberField.PlaceAbove.above (↥K) F v').under (𝓞 K) = v' :=
  HeightOneSpectrum.ext (NumberField.PlaceAbove.comap_above (↥K) F v')

theorem main (H : Subgroup (F ≃ₐ[E] F)) (v : HeightOneSpectrum (𝓞 E)) (w : HeightOneSpectrum (𝓞 F)) (hw : w.under (𝓞 E) = v) :
    Finite {v' : HeightOneSpectrum (𝓞 ↥(IntermediateField.fixedField H)) // v'.under (𝓞 E) = v} ∧
    ∃ g : {v' : HeightOneSpectrum (𝓞 ↥(IntermediateField.fixedField H)) // v'.under (𝓞 E) = v} → (F ≃ₐ[E] F),
      Function.Bijective (fun i => DoubleCoset.mk (NumberField.PlaceDecomp.decomp E F w) H (g i)) ∧
      (∃ i₀, i₀.1 = w.under (𝓞 ↥(IntermediateField.fixedField H)) ∧ g i₀ = 1) ∧
      (∀ i, ((g i)⁻¹ • w).under (𝓞 ↥(IntermediateField.fixedField H)) = i.1) ∧
      (∀ i, ∃ h : ↥H, (h : F ≃ₐ[E] F) • NumberField.PlaceAbove.above (↥(IntermediateField.fixedField H)) F i.1 = (g i)⁻¹ • w) ∧
      (∀ i, Nat.card ↥((MulAut.conj (g i) • H).subgroupOf (NumberField.PlaceDecomp.decomp E F w)) =
        Nat.card ↥(H ⊓ NumberField.PlaceDecomp.decomp E F
          (NumberField.PlaceAbove.above (↥(IntermediateField.fixedField H)) F i.1))) := by
  classical

  set K : IntermediateField E F := IntermediateField.fixedField H with hK

  have hf : ∀ σ : F ≃ₐ[E] F, ((σ • w).under (𝓞 K)).under (𝓞 E) = v := fun σ => by
    rw [under_under K, NumberField.PlaceTransport.under_smul E F σ w, hw]
  let f : (F ≃ₐ[E] F) → {v' : HeightOneSpectrum (𝓞 K) // v'.under (𝓞 E) = v} := fun σ => ⟨(σ • w).under (𝓞 K), hf σ⟩

  have hfs : Function.Surjective f := by
    rintro ⟨v', hv'⟩
    have h1 : (NumberField.PlaceAbove.above (↥K) F v').under (𝓞 E) = w.under (𝓞 E) := by
      rw [← under_under K, under_above K v', hv', hw]
    have hmem : NumberField.PlaceAbove.above (↥K) F v' ∈ MulAction.orbit (F ≃ₐ[E] F) w := by
      rw [NumberField.PlaceTransport.orbit_eq_setOf_under_eq E F w]; exact h1
    obtain ⟨σ, hσ⟩ := hmem
    change σ • w = _ at hσ
    refine ⟨σ, Subtype.ext ?_⟩
    change (σ • w).under (𝓞 K) = v'
    rw [hσ, under_above K v']
  refine ⟨Finite.of_surjective f hfs, ?_⟩

  let i₀ : {v' : HeightOneSpectrum (𝓞 K) // v'.under (𝓞 E) = v} := ⟨w.under (𝓞 K), by rw [under_under K, hw]⟩
  let g : {v' : HeightOneSpectrum (𝓞 K) // v'.under (𝓞 E) = v} → (F ≃ₐ[E] F) := fun i =>
    if i = i₀ then 1 else (Classical.choose (hfs i))⁻¹
  have hg_under : ∀ i, ((g i)⁻¹ • w).under (𝓞 K) = i.1 := by
    intro i
    by_cases hi : i = i₀
    · subst hi
      have : g i₀ = 1 := if_pos rfl
      rw [this, inv_one, one_smul]
    · have : g i = (Classical.choose (hfs i))⁻¹ := if_neg hi
      rw [this, inv_inv]
      exact congrArg Subtype.val (Classical.choose_spec (hfs i))

  have hconj : ∀ i, ∃ h : ↥H, (h : F ≃ₐ[E] F) • NumberField.PlaceAbove.above (↥K) F i.1 = (g i)⁻¹ • w := fun i =>
    exists_mem_smul_eq_of_under_eq H _ _ (by rw [under_above K, hg_under])
  refine ⟨g, ⟨?_, ?_⟩, ⟨i₀, rfl, if_pos rfl⟩, hg_under, hconj, ?_⟩
  ·
    intro i j hij
    obtain ⟨d, hd, h, hh, hgj⟩ := (DoubleCoset.eq (NumberField.PlaceDecomp.decomp E F w) H (g i) (g j)).1 hij
    apply Subtype.ext
    rw [← hg_under i, ← hg_under j, hgj, mul_inv_rev, mul_inv_rev, mul_smul, mul_smul,
      ((mem_decomp_iff _ w).1 ((NumberField.PlaceDecomp.decomp E F w).inv_mem hd)),
      under_smul_of_mem H (H.inv_mem hh)]
  ·
    intro q
    induction q using Quotient.inductionOn with
    | h x =>
      let i := f x⁻¹
      obtain ⟨h, hh⟩ := exists_mem_smul_eq_of_under_eq H ((g i)⁻¹ • w) (x⁻¹ • w) (by
        rw [hg_under])
      refine ⟨i, ?_⟩
      change DoubleCoset.mk _ _ (g i) = DoubleCoset.mk _ _ x
      rw [DoubleCoset.eq]
      refine ⟨x * (h : F ≃ₐ[E] F) * (g i)⁻¹, ?_, (h : F ≃ₐ[E] F)⁻¹, H.inv_mem h.2, by group⟩
      rw [mem_decomp_iff, mul_smul, mul_smul, hh, smul_inv_smul]
  ·
    intro i
    obtain ⟨h, hh⟩ := hconj i

    refine Nat.card_congr
      { toFun := fun x => ⟨(h : F ≃ₐ[E] F)⁻¹ * ((g i)⁻¹ * ((x : ↥(NumberField.PlaceDecomp.decomp E F w)) : F ≃ₐ[E] F) * g i) * h, ?_⟩
        invFun := fun y => ⟨⟨g i * ((h : F ≃ₐ[E] F) * (y : F ≃ₐ[E] F) * (h : F ≃ₐ[E] F)⁻¹) * (g i)⁻¹, ?_⟩, ?_⟩
        left_inv := fun x => by apply Subtype.ext; apply Subtype.ext; change _ = ((x : ↥(NumberField.PlaceDecomp.decomp E F w)) : F ≃ₐ[E] F); group
        right_inv := fun y => by apply Subtype.ext; change _ = (y : F ≃ₐ[E] F); group }
    ·
      have hx := x.2
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_pointwise_smul_iff_inv_smul_mem, MulAut.smul_def, MulAut.conj_inv_apply] at hx
      have hxw : ((x : ↥(NumberField.PlaceDecomp.decomp E F w)) : F ≃ₐ[E] F) • w = w :=
        (mem_decomp_iff _ w).1 (x : ↥(NumberField.PlaceDecomp.decomp E F w)).2
      refine Subgroup.mem_inf.2 ⟨H.mul_mem (H.mul_mem (H.inv_mem h.2) hx) h.2, ?_⟩
      rw [mem_decomp_iff, mul_smul, mul_smul, hh, mul_smul, mul_smul, smul_inv_smul, hxw, ← hh, inv_smul_smul]
    ·
      obtain ⟨hyH, hyD⟩ := Subgroup.mem_inf.1 y.2
      rw [mem_decomp_iff] at hyD
      rw [mem_decomp_iff, mul_smul, mul_smul, mul_smul, mul_smul, ← hh, inv_smul_smul, hyD, hh, smul_inv_smul]
    ·
      obtain ⟨hyH, hyD⟩ := Subgroup.mem_inf.1 y.2
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_pointwise_smul_iff_inv_smul_mem, MulAut.smul_def, MulAut.conj_inv_apply]
      have : (g i)⁻¹ * (g i * ((h : F ≃ₐ[E] F) * (y : F ≃ₐ[E] F) * (h : F ≃ₐ[E] F)⁻¹) * (g i)⁻¹) * g i
          = (h : F ≃ₐ[E] F) * (y : F ≃ₐ[E] F) * (h : F ≃ₐ[E] F)⁻¹ := by group
      rw [this]
      exact H.mul_mem (H.mul_mem h.2 hyH) (H.inv_mem h.2)

end NumberField.PlaceTransport.Dict

theorem solution
    (E F : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F] [IsGalois E F]
    (H : Subgroup (F ≃ₐ[E] F)) (v : HeightOneSpectrum (𝓞 E)) (w : HeightOneSpectrum (𝓞 F)) (hw : w.under (𝓞 E) = v) :
    Finite {v' : HeightOneSpectrum (𝓞 ↥(IntermediateField.fixedField H)) // v'.under (𝓞 E) = v} ∧
    ∃ g : {v' : HeightOneSpectrum (𝓞 ↥(IntermediateField.fixedField H)) // v'.under (𝓞 E) = v} → (F ≃ₐ[E] F),
      Function.Bijective (fun i => DoubleCoset.mk (NumberField.PlaceDecomp.decomp E F w) H (g i)) ∧
      (∃ i₀, i₀.1 = w.under (𝓞 ↥(IntermediateField.fixedField H)) ∧ g i₀ = 1) ∧
      (∀ i, ((g i)⁻¹ • w).under (𝓞 ↥(IntermediateField.fixedField H)) = i.1) ∧
      (∀ i, ∃ h : ↥H, (h : F ≃ₐ[E] F) • NumberField.PlaceAbove.above (↥(IntermediateField.fixedField H)) F i.1 = (g i)⁻¹ • w) ∧
      (∀ i, Nat.card ↥((MulAut.conj (g i) • H).subgroupOf (NumberField.PlaceDecomp.decomp E F w)) =
        Nat.card ↥(H ⊓ NumberField.PlaceDecomp.decomp E F
          (NumberField.PlaceAbove.above (↥(IntermediateField.fixedField H)) F i.1))) :=
  NumberField.PlaceTransport.Dict.main H v w hw

end S_NumberField_PlaceTransport_exists_bijective_doubleCoset_decomp_of_under_eq
end P2MW
export P2MW.S_NumberField_PlaceTransport_exists_bijective_doubleCoset_decomp_of_under_eq (solution)
