-- Prove2me | solution 1 for M4aHerbrand.exists_map_eq_of_map_eq_zero_groupCohomology_ideles_of_isCyclic
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/436761da-d3a3-5627-8b60-e38093de1d88

import Mathlib
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_NumberField_ArchimedeanIdeleModule
import Definitions.Def_NumberField_SIdeleModule
import Definitions.Def_NumberField_PlaceAbove
import Definitions.Def_ExtCitation_LocalLevel_FundamentalClass
import Definitions.Def_GroupCohomology_CyclicCarry
import Theorems.Thm_groupCohomology_exists_carry_H2pi_eq
import Theorems.Thm_groupCohomology_map_carry_H2pi_eq_smul_carry
import Theorems.Thm_groupCohomology_carryFun_mem_cocycles2
import Theorems.Thm_groupCohomology_carry_H2pi_eq_zero_iff
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_M4aHerbrand_exists_map_eq_of_map_eq_zero_groupCohomology_ideles_of_isCyclic
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000
p2m_open "CategoryTheory NumberField IsDedekindDomain M4aHerbrand P2MW.S_M4aHerbrand_exists_map_eq_of_map_eq_zero_groupCohomology_ideles_of_isCyclic.M4aHerbrand"
open scoped NumberField.PlaceDecomp

namespace M4aHerbrand
p2m_export "M4aHerbrand" "principalIdeles IdeleClassGroup IdeleGaloisDescent"
namespace C6K
p2m_open "M4aHerbrand"
open groupCohomology

theorem map_id_H2π_carryFun {Q : Type} [Group Q] (t : Q) (ht : ∀ g : Q, g ∈ Subgroup.zpowers t) (hfin : IsOfFinOrder t)
    (A B : Rep ℤ Q) (φ : A ⟶ B) (a : A) (ha : A.ρ t a = a)
    (hza : carryFun t ht hfin a ∈ cocycles₂ A) (hzb : carryFun t ht hfin (φ.hom a) ∈ cocycles₂ B) :
    (groupCohomology.map (MonoidHom.id Q) φ 2).hom ((H2π A).hom ⟨carryFun t ht hfin a, hza⟩) =
      (H2π B).hom ⟨carryFun t ht hfin (φ.hom a), hzb⟩ := by
  have h := groupCohomology.map_carry_H2pi_eq_smul_carry (MonoidHom.id Q) Function.injective_id t ht hfin 1 t
    (by rw [pow_one]; rfl) ht hfin A B φ a ha hza hzb
  rwa [Nat.gcd_one_right, Nat.div_one, one_smul] at h

theorem carryFun_add {G : Type} [Group G] (s : G) (hs : ∀ g : G, g ∈ Subgroup.zpowers s) (hfin : IsOfFinOrder s)
    {A : Rep ℤ G} (x y : A) :
    carryFun s hs hfin (x + y) = carryFun s hs hfin x + carryFun s hs hfin y := by
  funext p
  simp only [carryFun, Pi.add_apply]
  split_ifs <;> simp

theorem ρ_norm_eq {Q : Type} [Group Q] (t : Q) {Mu : Type} [CommGroup Mu] [MulDistribMulAction Q Mu]
    (b : Rep.ofMulDistribMulAction Q Mu) :
    (Rep.ofMulDistribMulAction Q Mu).ρ t (∑ i ∈ Finset.range (orderOf t), (Rep.ofMulDistribMulAction Q Mu).ρ (t ^ i) b) =
      ∑ i ∈ Finset.range (orderOf t), (Rep.ofMulDistribMulAction Q Mu).ρ (t ^ i) b := by
  rw [map_sum]
  have h1 : ∀ i, (Rep.ofMulDistribMulAction Q Mu).ρ t ((Rep.ofMulDistribMulAction Q Mu).ρ (t ^ i) b) =
      (Rep.ofMulDistribMulAction Q Mu).ρ (t ^ (i + 1)) b := fun i => by
    rw [← Module.End.mul_apply, ← map_mul, pow_succ']
  simp_rw [h1]
  rcases Nat.eq_zero_or_pos (orderOf t) with h0 | hpos
  · rw [h0, Finset.sum_range_zero, Finset.sum_range_zero]
  · obtain ⟨m, hm⟩ : ∃ m, orderOf t = m + 1 := ⟨orderOf t - 1, by omega⟩
    have htop : (Rep.ofMulDistribMulAction Q Mu).ρ (t ^ (m + 1)) b = (Rep.ofMulDistribMulAction Q Mu).ρ (t ^ 0) b := by
      rw [← hm, pow_orderOf_eq_one, pow_zero]
    rw [hm, Finset.sum_range_succ, Finset.sum_range_succ' (fun i => (Rep.ofMulDistribMulAction Q Mu).ρ (t ^ i) b), htop]

end M4aHerbrand.C6K

open M4aHerbrand.C6K groupCohomology in
theorem solution
    (E F : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F] [IsGalois E F]
    [IsCyclic (F ≃ₐ[E] F)]
    (D : IdeleGaloisDescent (𝓞 F) E F)

    [MulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ]
    (hactI : ∀ (g : (F ≃ₐ[E] F)) (x : (AdeleRing (𝓞 F) F)ˣ), g • x = D.unitsAct g x)
    [MulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)]
    (hact : ∀ (g : (F ≃ₐ[E] F)) (c : IdeleClassGroup (𝓞 F) F), g • c = D.classAct g c)

    [MulDistribMulAction (F ≃ₐ[E] F) Fˣ]
    (hactF : ∀ (g : (F ≃ₐ[E] F)) (a : Fˣ), ((g • a : Fˣ) : F) = g (a : F))
    (j : (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) Fˣ) ⟶ (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ))
    (hj : ∀ a : Fˣ, j.hom (Additive.ofMul a) = Additive.ofMul (Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F) a))

    (π : (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ) ⟶ (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)))
    (hπ : ∀ x : (AdeleRing (𝓞 F) F)ˣ, π.hom (Additive.ofMul x) = Additive.ofMul (QuotientGroup.mk x : IdeleClassGroup (𝓞 F) F))
    (x : ↥(groupCohomology (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ) 2))
    (hx : (groupCohomology.map (MonoidHom.id (F ≃ₐ[E] F)) π 2).hom x = 0) :
    ∃ α : ↥(groupCohomology (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) Fˣ) 2), (groupCohomology.map (MonoidHom.id (F ≃ₐ[E] F)) j 2).hom α = x := by
  classical
  haveI : Fintype (F ≃ₐ[E] F) := Fintype.ofFinite _
  obtain ⟨s, hs⟩ := IsCyclic.exists_generator (α := F ≃ₐ[E] F)
  have hfin : IsOfFinOrder s := isOfFinOrder_of_finite s

  induction x using H2_induction_on with
  | h z =>
    obtain ⟨hρa, hmem, heq⟩ := groupCohomology.exists_carry_H2pi_eq s hs hfin z
    set a : Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ := cyclicInv s ⇑z with ha

    have hzπ : carryFun s hs hfin (π.hom a) ∈ cocycles₂ (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)) :=
      groupCohomology.carryFun_mem_cocycles2 s hs hfin _ (by rw [← Rep.hom_comm_apply, hρa])
    have h0 : (H2π _).hom ⟨carryFun s hs hfin (π.hom a), hzπ⟩ = 0 := by
      rw [← map_id_H2π_carryFun s hs hfin _ _ π a hρa hmem hzπ, heq]; exact hx
    obtain ⟨b, hb⟩ := (groupCohomology.carry_H2pi_eq_zero_iff s hs hfin (π.hom a) (by rw [← Rep.hom_comm_apply, hρa]) hzπ).1 h0

    obtain ⟨y, hy⟩ := QuotientGroup.mk_surjective (Additive.toMul (α := IdeleClassGroup (𝓞 F) F) b)
    have hby : π.hom (Additive.ofMul y) = b := by rw [hπ, hy]; rfl
    set Ny : Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ :=
      ∑ i ∈ Finset.range (orderOf s), (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ).ρ (s ^ i) (Additive.ofMul y) with hNy
    have hπNy : π.hom Ny = π.hom a := by
      rw [hNy, map_sum, ← hb]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [Rep.hom_comm_apply, hby]
    have hρNy : (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ).ρ s Ny = Ny := ρ_norm_eq s (Additive.ofMul y)

    have hdiff : Additive.toMul (α := (AdeleRing (𝓞 F) F)ˣ) (a - Ny) ∈ principalIdeles (𝓞 F) F := by
      rw [← QuotientGroup.eq_one_iff]
      have h1 : π.hom (a - Ny) = 0 := by rw [map_sub, hπNy, sub_self]
      have h2 : π.hom (a - Ny) = Additive.ofMul (QuotientGroup.mk (Additive.toMul (α := (AdeleRing (𝓞 F) F)ˣ) (a - Ny)) :
          IdeleClassGroup (𝓞 F) F) := hπ _
      rw [h2] at h1
      exact Additive.ofMul.injective h1
    obtain ⟨f₀, hf₀⟩ := hdiff
    have hjf : j.hom (Additive.ofMul f₀) = a - Ny := by rw [hj, hf₀]; rfl

    have hinjA : Function.Injective (algebraMap F (AdeleRing (𝓞 F) F)) := NumberField.AdeleRing.algebraMap_injective (𝓞 F) F
    have hρf : (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) Fˣ).ρ s (Additive.ofMul f₀) = Additive.ofMul f₀ := by
      have h1 : j.hom ((Rep.ofMulDistribMulAction (F ≃ₐ[E] F) Fˣ).ρ s (Additive.ofMul f₀)) = j.hom (Additive.ofMul f₀) := by
        rw [Rep.hom_comm_apply, hjf, map_sub, hρa, hρNy]
      rw [Rep.ofMulDistribMulAction_ρ_apply_apply] at h1
      change j.hom (Additive.ofMul (s • f₀)) = j.hom (Additive.ofMul f₀) at h1
      rw [hj, hj] at h1
      have h2 := Additive.ofMul.injective h1
      have h3 : ((Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F) (s • f₀) : AdeleRing (𝓞 F) F)) =
          (Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F) f₀ : AdeleRing (𝓞 F) F) := congrArg Units.val h2
      rw [Units.coe_map, Units.coe_map] at h3
      rw [Rep.ofMulDistribMulAction_ρ_apply_apply]
      exact congrArg Additive.ofMul (Units.ext (hinjA h3))

    have hzN := groupCohomology.carryFun_mem_cocycles2 s hs hfin Ny hρNy
    have hρjf : (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ).ρ s (j.hom (Additive.ofMul f₀)) = j.hom (Additive.ofMul f₀) := by
      rw [← Rep.hom_comm_apply, hρf]
      rfl
    have hzj := groupCohomology.carryFun_mem_cocycles2 s hs hfin _ hρjf
    have hzf := groupCohomology.carryFun_mem_cocycles2 s hs hfin _ hρf
    have hNzero : (H2π (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ)).hom ⟨carryFun s hs hfin Ny, hzN⟩ = 0 :=
      (groupCohomology.carry_H2pi_eq_zero_iff s hs hfin Ny hρNy hzN).2 ⟨Additive.ofMul y, rfl⟩
    refine ⟨(H2π _).hom ⟨carryFun s hs hfin (Additive.ofMul f₀), hzf⟩, ?_⟩
    rw [map_id_H2π_carryFun s hs hfin _ _ j (Additive.ofMul f₀) hρf hzf hzj, ← heq]
    have hsplit : (⟨carryFun s hs hfin a, hmem⟩ : cocycles₂ (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ)) =
        ⟨carryFun s hs hfin Ny, hzN⟩ + ⟨carryFun s hs hfin (j.hom (Additive.ofMul f₀)), hzj⟩ := by
      apply Subtype.ext
      change carryFun s hs hfin a = carryFun s hs hfin Ny + carryFun s hs hfin (j.hom (Additive.ofMul f₀))
      rw [← carryFun_add, hjf, add_sub_cancel]
    rw [hsplit, map_add, hNzero, zero_add]

end S_M4aHerbrand_exists_map_eq_of_map_eq_zero_groupCohomology_ideles_of_isCyclic
end P2MW
export P2MW.S_M4aHerbrand_exists_map_eq_of_map_eq_zero_groupCohomology_ideles_of_isCyclic (solution)
