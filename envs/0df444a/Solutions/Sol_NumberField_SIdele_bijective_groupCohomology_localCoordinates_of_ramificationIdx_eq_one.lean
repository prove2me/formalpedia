-- Prove2me | solution 1 for NumberField.SIdele.bijective_groupCohomology_localCoordinates_of_ramificationIdx_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/dd4e2b9f-d9c9-5b2f-b758-2eab9e62e653

import Mathlib
import Definitions.Def_NumberField_SIdeleModule
import Theorems.Thm_GroupCohomology_RepPi_bijective_pi_map_proj
import Theorems.Thm_NumberField_PlaceDecomp_subsingleton_tateCohomology_integerUnits_of_ramificationIdx_eq_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_SIdele_bijective_groupCohomology_localCoordinates_of_ramificationIdx_eq_one

set_option autoImplicit false
p2m_open "IsDedekindDomain NumberField P2MW.S_NumberField_SIdele_bijective_groupCohomology_localCoordinates_of_ramificationIdx_eq_one.NumberField CategoryTheory"
open scoped NumberField.PlaceDecomp NumberField.InfPlaceDecomp

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 80000
set_option Elab.async false

open scoped NumberField.PlaceDecomp
open scoped NumberField.InfPlaceDecomp

namespace NumberField
p2m_export "NumberField" "mk InfinitePlace SIdele.fibre SIdele.obj PlaceAbove.above PlaceDecomp.decomp FiniteSIdele.D FiniteSIdele.localUnits FiniteSIdele.localIntegerUnits SUnits.under_above InfPlaceDecomp.localUnits ArchIdele.above PlaceDecomp.subsingleton_tateCohomology_integerUnits_of_ramificationIdx_eq_one"
namespace SIdele
p2m_export "NumberField.SIdele" "fibre obj"
namespace Ws25E1
p2m_open "NumberField.SIdele NumberField"

open CategoryTheory

theorem subsingleton_of_iso {k : Type} [CommRing k] {X Y : ModuleCat k} (e : X ≅ Y) [Subsingleton Y] : Subsingleton X :=
  e.toLinearEquiv.toEquiv.subsingleton

theorem bijective_forget {α β γ : Type} {T : (α ⊕ β) ⊕ γ → Type} {A' : α → Type} {C' : γ → Type}
    (hB : ∀ b, Subsingleton (T (Sum.inl (Sum.inr b)))) (zB : ∀ b, T (Sum.inl (Sum.inr b)))
    (eA : ∀ a, T (Sum.inl (Sum.inl a)) ≃ A' a) (eC : ∀ c, T (Sum.inr c) ≃ C' c) :
    Function.Bijective (fun y : (∀ i : (α ⊕ β) ⊕ γ, T i) =>
      ((fun a : α => eA a (y (Sum.inl (Sum.inl a)))), (fun c : γ => eC c (y (Sum.inr c))))) := by
  constructor
  · intro y y' h
    simp only [Prod.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    funext i
    rcases i with (a | b) | c
    · exact (eA a).injective (congrFun h1 a)
    · exact (hB b).elim _ _
    · exact (eC c).injective (congrFun h2 c)
  · rintro ⟨f, g⟩
    refine ⟨fun i => match i with
      | Sum.inl (Sum.inl a) => (eA a).symm (f a)
      | Sum.inl (Sum.inr b) => zB b
      | Sum.inr c => (eC c).symm (g c), ?_⟩
    simp only [Equiv.apply_symm_apply]

end NumberField.SIdele.Ws25E1

open NumberField.SIdele.Ws25E1 in
theorem solution (E K : Type) [Field E] [NumberField E]
    [Field K] [NumberField K] [Algebra E K] [IsGalois E K] (S : Finset (HeightOneSpectrum (𝓞 E)))
    (hunr : ∀ w : HeightOneSpectrum (𝓞 K), w.under (𝓞 E) ∉ S → (w.under (𝓞 E)).asIdeal.ramificationIdx' w.asIdeal = 1)
    (n : ℕ) :
    Function.Bijective (fun x : groupCohomology (NumberField.SIdele.obj E K S) (n + 1) =>
      ((fun v : {v // v ∈ S} =>
          (groupCohomology.map (MonoidHom.id (K ≃ₐ[E] K))
              (GroupCohomology.RepPi.proj (NumberField.SIdele.fibre E K S) (Sum.inl (Sum.inl v))) (n + 1) ≫
            (groupCohomology.coindIso (NumberField.FiniteSIdele.localUnits E K v.1) (n + 1)).hom).hom x),
       (fun v : InfinitePlace E =>
          (groupCohomology.map (MonoidHom.id (K ≃ₐ[E] K))
              (GroupCohomology.RepPi.proj (NumberField.SIdele.fibre E K S) (Sum.inr v)) (n + 1) ≫
            (groupCohomology.coindIso (NumberField.InfPlaceDecomp.localUnits E K (NumberField.ArchIdele.above E K v)) (n + 1)).hom).hom x))) := by
  classical

  have hΦ := GroupCohomology.RepPi.bijective_pi_map_proj (NumberField.SIdele.fibre E K S) (n + 1)

  have hB : ∀ v : {v // v ∉ S}, Subsingleton (groupCohomology (NumberField.SIdele.fibre E K S (Sum.inl (Sum.inr v))) (n + 1)) := by
    intro v
    have hw : ((NumberField.PlaceAbove.above E K v.1).under (𝓞 E)).asIdeal.ramificationIdx' (NumberField.PlaceAbove.above E K v.1).asIdeal = 1 :=
      hunr _ (by rw [NumberField.SUnits.under_above]; exact v.2)
    letI : Fintype (NumberField.PlaceDecomp.decomp E K (NumberField.PlaceAbove.above E K v.1)) := Fintype.ofFinite _
    have hsub := NumberField.PlaceDecomp.subsingleton_tateCohomology_integerUnits_of_ramificationIdx_eq_one E K
      (NumberField.PlaceAbove.above E K v.1) hw ((n + 1 : ℕ) : ℤ)
    rw [Rep.tateCohomology_ofNat_succ] at hsub
    show Subsingleton (groupCohomology (Rep.coind (NumberField.FiniteSIdele.D E K v.1).subtype (NumberField.FiniteSIdele.localIntegerUnits E K v.1)) (n + 1))
    exact subsingleton_of_iso (groupCohomology.coindIso (NumberField.FiniteSIdele.localIntegerUnits E K v.1) (n + 1))

  have hg := bijective_forget (α := {v // v ∈ S}) (β := {v // v ∉ S}) (γ := InfinitePlace E)
    (T := fun i => groupCohomology (NumberField.SIdele.fibre E K S i) (n + 1)) hB (fun _ => 0)
    (fun v => (groupCohomology.coindIso (NumberField.FiniteSIdele.localUnits E K v.1) (n + 1)).toLinearEquiv.toEquiv)
    (fun v => (groupCohomology.coindIso (NumberField.InfPlaceDecomp.localUnits E K (NumberField.ArchIdele.above E K v)) (n + 1)).toLinearEquiv.toEquiv)
  have key := hg.comp hΦ
  exact key

end S_NumberField_SIdele_bijective_groupCohomology_localCoordinates_of_ramificationIdx_eq_one
end P2MW
export P2MW.S_NumberField_SIdele_bijective_groupCohomology_localCoordinates_of_ramificationIdx_eq_one (solution)
