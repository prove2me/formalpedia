-- Prove2me | solution 1 for HopfAlgebra.exists_inertiaStable_simple_step_of_map_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/5083643d-b4a7-5c70-9a34-50776d515ebd

import Definitions.Def_GaloisRep_Flat
import Definitions.Def_GaloisRep_TameCharacter
import Definitions.Def_FLTPrelim_Ramification
import Mathlib.GroupTheory.PGroup
import Mathlib.GroupTheory.Index
import Theorems.Thm_GaloisRep_exists_finiteFlat_sub_of_equivariant_injection
import Theorems.Thm_GaloisRep_natCard_withConv_algHom_eq_finrank_of_finiteFlatHopf
import Mathlib.Algebra.Group.TypeTags.Basic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HopfAlgebra_exists_inertiaStable_simple_step_of_map_ne_zero

set_option autoImplicit false
set_option maxHeartbeats 3200000

theorem JH.finite_algHom {R : Type} [CommRing R] {G : Type} [CommRing G] [Algebra R G]
    [Module.Finite R G] {K : Type} [Field K] [Algebra R K] :
    Finite (G →ₐ[R] K) := by
  have li0 := linearIndependent_monoidHom G K
  have hinj : Function.Injective (fun φ : G →ₐ[R] K => (φ : G →* K)) := by
    intro p q hpq; exact DFunLike.ext _ _ fun x => DFunLike.congr_fun hpq x
  have li1 : LinearIndependent K (fun φ : G →ₐ[R] K => ((φ : G →* K) : G → K)) :=
    li0.comp _ hinj
  let c : (G →ₗ[R] K) →ₗ[K] (G → K) :=
    { toFun := fun f => ⇑f, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  have li2 : LinearIndependent K (fun φ : G →ₐ[R] K => φ.toLinearMap) :=
    LinearIndependent.of_comp c li1
  obtain ⟨n, ℓ, hℓ⟩ := Module.Finite.exists_fin' R G
  let D : (G →ₗ[R] K) →ₗ[K] ((Fin n → R) →ₗ[R] K) :=
    { toFun := fun f => f.comp ℓ
      map_add' := fun f g => rfl
      map_smul' := fun a f => rfl }
  have hD : Function.Injective D := by
    intro f g hfg
    refine LinearMap.ext fun x => ?_
    obtain ⟨y, rfl⟩ := hℓ x
    exact DFunLike.congr_fun hfg y
  haveI : Module.Finite K ((Fin n → R) →ₗ[R] K) :=
    Module.Finite.equiv ((Pi.basisFun R (Fin n)).constr K)
  haveI : Module.Finite K (G →ₗ[R] K) := Module.Finite.of_injective D hD
  exact li2.finite

theorem solution
    {p : ℕ} (hp : p.Prime)
    {H : Type} [CommRing H] [HopfAlgebra (GaloisRep.ratLocalizedAt p) H]
    [Module.Finite (GaloisRep.ratLocalizedAt p) H] [Module.Flat (GaloisRep.ratLocalizedAt p) H]
    [Coalgebra.IsCocomm (GaloisRep.ratLocalizedAt p) H]
    (hMp : ∀ f : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ), f ^ p = 1)
    (P : ValuationSubring (AlgebraicClosure ℚ))
    (N : Type) [AddCommGroup N]
    (F : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ) → N)
    (hFmul : ∀ f g : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ),
      F (f * g) = F f + F g)
    (K₀ : Submonoid (WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)))
    (hK₀ : (∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ f ∈ K₀,
      ∀ g : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ),
        (∀ h : H, g h = σ (f h)) → g ∈ K₀))
    (hFK₀ : ∃ f ∈ K₀, F f ≠ 0) :
    ∃ K K' : Submonoid (WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)),
      K ≤ K' ∧ K' ≤ K₀ ∧
      (∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ f ∈ K,
        ∀ g : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ),
          (∀ h : H, g h = σ (f h)) → g ∈ K) ∧
      (∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ f ∈ K',
        ∀ g : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ),
          (∀ h : H, g h = σ (f h)) → g ∈ K') ∧
      (∀ S : Submonoid (WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)),
        K ≤ S → S ≤ K' →
        (∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ f ∈ S,
          ∀ g : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ),
            (∀ h : H, g h = σ (f h)) → g ∈ S) →
        S = K ∨ S = K') ∧
      (∀ f ∈ K, F f = 0) ∧ (∃ f ∈ K', F f ≠ 0) ∧
      ∃ s : ℕ, 1 ≤ s ∧ Nat.card K' = p ^ s * Nat.card K := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩

  let Stab : Submonoid (WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)) → Prop := fun S =>
    ∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ f ∈ S, ∀ g : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ),
      (∀ h : H, g h = σ (f h)) → g ∈ S

  letI instG : CommGroup (WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)) :=
    commGroupOfIsUnit fun f => IsUnit.of_pow_eq_one (hMp f) hp.ne_zero

  have hinv_eq : ∀ f : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ),
      f⁻¹ = f ^ (p - 1) := fun f =>
    inv_eq_of_mul_eq_one_right (by rw [← pow_succ', Nat.sub_add_cancel hp.one_le, hMp])

  haveI hfinA : Finite (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ) := JH.finite_algHom
  haveI hfin : Finite (WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)) :=
    Finite.of_equiv _ (WithConv.equiv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)).symm
  haveI : Finite (Submonoid (WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ))) :=
    Finite.of_injective (fun S : Submonoid (WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)) => (S : Set (WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ))))
      SetLike.coe_injective
  have hF1 : F 1 = 0 := by
    have h := (hFmul 1 1).symm; rw [one_mul] at h
    exact add_left_cancel (h.trans (add_zero (F 1)).symm)

  let A : Set (Submonoid (WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ))) := {S | S ≤ K₀ ∧ Stab S ∧ ∃ f ∈ S, F f ≠ 0}
  have hAne : A.Nonempty := ⟨K₀, le_rfl, hK₀, hFK₀⟩
  obtain ⟨K', ⟨hK'K₀, hK'stab, hFK'⟩, hK'min⟩ := (wellFounded_lt (α := Submonoid (WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)))).has_min A hAne

  have hStabBot : Stab ⊥ := by
    intro σ _ f hf g hg
    rw [Submonoid.mem_bot] at hf ⊢
    subst hf
    apply WithConv.ofConv_injective
    apply AlgHom.ext
    intro h
    rw [hg h, AlgHom.convOne_apply]
    exact (σ.toAlgHom.restrictScalars (GaloisRep.ratLocalizedAt p)).commutes _
  let B : Set (Submonoid (WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ))) := {S | S < K' ∧ Stab S}
  have hBne : B.Nonempty := by
    refine ⟨⊥, lt_of_le_of_ne bot_le ?_, hStabBot⟩
    intro hbot
    obtain ⟨f, hf, hFf⟩ := hFK'
    rw [← hbot, Submonoid.mem_bot] at hf
    exact hFf (hf ▸ hF1)
  obtain ⟨K, ⟨hKK', hKstab⟩, hKmax⟩ := (wellFounded_gt (α := Submonoid (WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)))).has_min B hBne
  refine ⟨K, K', hKK'.le, hK'K₀, hKstab, hK'stab, ?_, ?_, hFK', ?_⟩
  ·
    intro S hKS hSK' hSstab
    rcases hSK'.lt_or_eq with hlt | heq
    · left
      by_contra hne
      exact hKmax S ⟨hlt, hSstab⟩ (lt_of_le_of_ne hKS (Ne.symm hne))
    · right; exact heq
  ·
    intro f hf
    by_contra hFf
    exact hK'min K ⟨hKK'.le.trans hK'K₀, hKstab, f, hf, hFf⟩ hKK'
  ·
    have hinv : ∀ (S : Submonoid (WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)))
        (f : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)), f ∈ S → f⁻¹ ∈ S :=
      fun S f hf => by rw [hinv_eq f]; exact pow_mem hf (p - 1)
    let Ksg : Subgroup (WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)) :=
      { K with inv_mem' := fun {f} hf => hinv K f hf }
    let K'sg : Subgroup (WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)) :=
      { K' with inv_mem' := fun {f} hf => hinv K' f hf }
    have hle : Ksg ≤ K'sg := fun f hf => hKK'.le hf
    have hne : Ksg ≠ K'sg := fun h => hKK'.ne (congrArg Subgroup.toSubmonoid h)
    have hPG : IsPGroup p (WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)) :=
      fun g => ⟨1, by rw [pow_one]; exact hMp g⟩
    obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp (hPG.to_subgroup K'sg)
    obtain ⟨b, hb⟩ := IsPGroup.iff_card.mp (hPG.to_subgroup Ksg)
    have hlt : Nat.card Ksg < Nat.card K'sg :=
      lt_of_not_ge fun hge => hne (Subgroup.eq_of_le_of_card_ge hle hge)
    rw [ha, hb] at hlt
    have hba : b < a := (Nat.pow_lt_pow_iff_right hp.one_lt).mp hlt
    refine ⟨a - b, Nat.sub_pos_of_lt hba, ?_⟩
    have ha' : Nat.card K' = p ^ a := ha
    have hb' : Nat.card K = p ^ b := hb
    rw [ha', hb', ← pow_add, Nat.sub_add_cancel hba.le]

end S_HopfAlgebra_exists_inertiaStable_simple_step_of_map_ne_zero
end P2MW
export P2MW.S_HopfAlgebra_exists_inertiaStable_simple_step_of_map_ne_zero (solution)
