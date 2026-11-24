-- Prove2me | solution 1 for GlobalTheory.exists_unitary_char_of_open_subgroup_and_hom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:44:28.1263+00:00
-- url     : https://prove2.me/submissions/cde7e924-101e-459f-bdf7-dce990efe7b3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsContinuousCircleCharExtension
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsUnitaryCharOfOpenSubgroupAndHom
import Theorems.Thm_GlobalTheory_toUnits_unitaryCharToCircle
import Theorems.Thm_GlobalTheory_exists_continuous_circle_char_extension

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open NumberField IsDedekindDomain
namespace GlobalTheory
private lemma continuous_toUnits_comp {X : Type} [TopologicalSpace X] {f : X → Circle}
    (hf : Continuous f) : Continuous fun x => Circle.toUnits (f x) := by
  rw [Units.continuous_iff]
  refine ⟨continuous_subtype_val.comp hf, ?_⟩
  have h : (fun x => (((Circle.toUnits (f x))⁻¹ : ℂˣ) : ℂ)) = fun x => (((f x)⁻¹ : Circle) : ℂ) := by
    funext x
    simp
  rw [h]
  exact continuous_subtype_val.comp hf.inv
end GlobalTheory
end

set_option autoImplicit false
open NumberField IsDedekindDomain
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (G A : Type) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [CommGroup A] (U : Subgroup G), IsOpen (U : Set G) → ∀ (α : A →* G) (a : A →* ℂˣ) (ψ : G →* ℂˣ), Continuous ψ → (∀ x, ‖((ψ x : ℂˣ) : ℂ)‖ = 1) → (∀ y, ‖((a y : ℂˣ) : ℂ)‖ = 1) → (∀ y, α y ∈ U → a y = ψ (α y)) → ∃ χ : G →* ℂˣ, Continuous χ ∧ (∀ x, ‖((χ x : ℂˣ) : ℂ)‖ = 1) ∧ (∀ x ∈ U, χ x = ψ x) ∧ ∀ y, χ (α y) = a y := by
  intro G A _ _ _ _ U hU α a ψ hψc hψ ha hagree
  let _ : TopologicalSpace A := ⊥
  have _ : DiscreteTopology A := ⟨rfl⟩

  set ψ₁ : G →* Circle := unitaryCharToCircle ψ hψ
  set a₁ : A →* Circle := unitaryCharToCircle a ha
  have hψ₁c : Continuous ψ₁ := Continuous.subtype_mk (Units.continuous_val.comp hψc) _
  have hψ₁coe : ∀ x, ((ψ₁ x : Circle) : ℂ) = (ψ x : ℂ) := fun x => rfl
  have ha₁coe : ∀ y, ((a₁ y : Circle) : ℂ) = (a y : ℂ) := fun y => rfl

  let H : Subgroup (G × A) := U.prod ⊤
  have hH : IsOpen (H : Set (G × A)) := by
    simpa [H, Subgroup.coe_prod] using hU.prod isOpen_univ
  let N : Subgroup (G × A) := (MonoidHom.prod α (MonoidHom.id A)).range
  let φ : H →* Circle :=
    ((ψ₁.comp (MonoidHom.fst G A)) / (a₁.comp (MonoidHom.snd G A))).comp H.subtype
  have hφ : ∀ x : H, φ x = ψ₁ (x : G × A).1 / a₁ (x : G × A).2 := fun x => rfl
  have hφc : Continuous φ := by
    have h1 : Continuous fun x : H => ψ₁ (x : G × A).1 :=
      hψ₁c.comp (continuous_fst.comp continuous_subtype_val)
    have h2 : Continuous fun x : H => a₁ (x : G × A).2 :=
      continuous_of_discreteTopology.comp (continuous_snd.comp continuous_subtype_val)
    have hfun : (φ : H → Circle) = fun x : H => ψ₁ (x : G × A).1 / a₁ (x : G × A).2 := funext hφ
    rw [hfun]
    exact h1.div' h2

  have htriv : ∀ x : H, (x : G × A) ∈ N → φ x = 1 := by
    rintro ⟨x, hxH⟩ ⟨y, rfl⟩
    have hyU : α y ∈ U := (Subgroup.mem_prod.1 hxH).1
    change ψ₁ (α y) / a₁ y = 1
    rw [div_eq_one]
    apply Circle.ext
    rw [hψ₁coe, ha₁coe, hagree y hyU]
  obtain ⟨χ₂, hχ₂c, hχ₂N, hχ₂H⟩ :=
    exists_continuous_circle_char_extension (G × A) H N φ hH hφc htriv

  refine ⟨Circle.toUnits.comp (χ₂.comp (MonoidHom.inl G A)), ?_, ?_, ?_, ?_⟩
  · exact continuous_toUnits_comp (hχ₂c.comp (continuous_id.prodMk continuous_const))
  · intro x
    exact Circle.norm_coe _
  · intro x hx
    have hxH : ((x, 1) : G × A) ∈ H := Subgroup.mem_prod.2 ⟨hx, Subgroup.mem_top 1⟩
    have h : χ₂ (x, 1) = ψ₁ x / a₁ 1 := hχ₂H ⟨(x, 1), hxH⟩
    change Circle.toUnits (χ₂ (x, 1)) = ψ x
    rw [h, map_one, div_one]
    exact toUnits_unitaryCharToCircle ψ hψ x
  · intro y
    have hN : ((α y, y) : G × A) ∈ N := ⟨y, rfl⟩
    have h0 : χ₂ (α y, y) = 1 := hχ₂N _ hN
    have hyH : ((1, y) : G × A) ∈ H := Subgroup.mem_prod.2 ⟨U.one_mem, Subgroup.mem_top y⟩
    have h1 : χ₂ (1, y) = ψ₁ 1 / a₁ y := hχ₂H ⟨(1, y), hyH⟩
    have hsplit : ((α y, y) : G × A) = (α y, 1) * (1, y) :=
      Prod.ext (mul_one _).symm (one_mul _).symm
    rw [hsplit, map_mul, h1, map_one, one_div, mul_inv_eq_one] at h0
    change Circle.toUnits (χ₂ (α y, 1)) = a y
    rw [h0]
    exact toUnits_unitaryCharToCircle a ha y
end GlobalTheory
