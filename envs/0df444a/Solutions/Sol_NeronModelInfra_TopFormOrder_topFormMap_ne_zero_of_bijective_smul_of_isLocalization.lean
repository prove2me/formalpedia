-- Prove2me | solution 1 for NeronModelInfra.TopFormOrder.topFormMap_ne_zero_of_bijective_smul_of_isLocalization
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/64e3442c-7db3-5057-85d9-e5e596a1782f

import Mathlib
import Definitions.Def_NeronModelInfra_TopFormOrder
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NeronModelInfra_TopFormOrder_topFormMap_ne_zero_of_bijective_smul_of_isLocalization

set_option autoImplicit false

universe u

open NeronModelInfra NeronModelInfra.TopFormOrder

namespace P2mFrameNZ

theorem orderEmbedding_fin_eq_id {d : ℕ} (f : Fin d ↪o Fin d) : (f : Fin d → Fin d) = id := by
  have hs : Function.Surjective f := Finite.surjective_of_injective f.injective
  have h1 : Set.range (f : Fin d → Fin d) = Set.range (id : Fin d → Fin d) := by
    rw [Set.range_id, Set.range_eq_univ.mpr hs]
  exact (f.strictMono.range_inj strictMono_id).mp h1

theorem exists_smul_ιMulti_and_smul_injective {A M : Type u} [CommRing A] [AddCommGroup M] [Module A M]
    (d : ℕ) (b : Module.Basis (Fin d) A M) :
    (∀ η : ⋀[A]^d M, ∃ c : A, η = c • exteriorPower.ιMulti A d b) ∧
      ∀ c c' : A, c • exteriorPower.ιMulti A d b = c' • exteriorPower.ιMulti A d b → c = c' := by
  classical
  let B := b.exteriorPower d
  let s₀ : Set.powersetCard (Fin d) d := ⟨Finset.univ, by simp [Set.powersetCard]⟩
  have hs : ∀ s : Set.powersetCard (Fin d) d, s = s₀ := by
    intro s
    apply Subtype.ext
    show s.val = Finset.univ
    exact Finset.eq_univ_of_card s.val (by rw [Fintype.card_fin]; exact s.prop)
  have hB : B s₀ = exteriorPower.ιMulti A d b := by
    rw [show B s₀ = exteriorPower.ιMulti_family A d b s₀ from exteriorPower.basis_apply A d b s₀]
    unfold exteriorPower.ιMulti_family
    congr 1
    funext i
    show b ((Set.powersetCard.ofFinEmbEquiv.symm s₀ : Fin d ↪o Fin d) i) = b i
    rw [orderEmbedding_fin_eq_id]
    rfl
  refine ⟨fun η => ⟨B.repr η s₀, ?_⟩, fun c c' hc => ?_⟩
  · rw [← hB]
    conv_lhs => rw [← B.sum_repr η]
    rw [Fintype.sum_eq_single s₀ (fun s hs' => absurd (hs s) hs')]
  · rw [← hB] at hc
    have h := congrArg (fun x => B.repr x s₀) hc
    simpa [B.repr_self] using h

set_option backward.isDefEq.respectTransparency false in
theorem main
    (K A F : Type u) [Field K] [CommRing A] [Algebra K A] [Field F] [Algebra A F] [Algebra K F]
    [IsScalarTower K A F] (M : Submonoid A) [IsLocalization M F]
    (d : ℕ) (b : Module.Basis (Fin d) A (Ω[A⁄K]))
    (ω : ⋀[A]^d (Ω[A⁄K])) (hω : Function.Bijective fun g : A => g • ω) :
    topFormMap K K A F d ω ≠ 0 := by
  classical
  letI instA := moduleAlong A F (⋀[F]^d (Ω[F⁄K]))
  haveI : IsScalarTower A F (⋀[F]^d (Ω[F⁄K])) := IsScalarTower.of_algebraMap_smul fun _ _ => rfl

  obtain ⟨hspan, hfree⟩ := exists_smul_ιMulti_and_smul_injective d b
  obtain ⟨c, hc⟩ := hspan ω
  obtain ⟨g, hg⟩ := hω.2 (exteriorPower.ιMulti A d b)
  have hgc : g * c = 1 := by
    have h1 : (g * c) • exteriorPower.ιMulti A d b = (1 : A) • exteriorPower.ιMulti A d b := by
      rw [mul_smul, ← hc, one_smul]; exact hg
    exact hfree _ _ h1
  have hcU : IsUnit c := IsUnit.of_mul_eq_one g (by rw [mul_comm]; exact hgc)

  set v : Fin d → Ω[F⁄K] := fun i => KaehlerDifferential.map K K A F (b i) with hv
  have hρ : topFormMap K K A F d (exteriorPower.ιMulti A d b) = exteriorPower.ιMulti F d v := by
    show exteriorPower.alternatingMapLinearEquiv (ιMultiAlong K K A F d) (exteriorPower.ιMulti A d b) = _
    rw [exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
    rfl
  haveI : IsLocalizedModule M (KaehlerDifferential.map K K A F) :=
    KaehlerDifferential.isLocalizedModule_map K A F M
  let bF : Module.Basis (Fin d) F (Ω[F⁄K]) := b.ofIsLocalizedModule F M (KaehlerDifferential.map K K A F)
  have hbF : (bF : Fin d → Ω[F⁄K]) = v := by
    funext i
    simp only [bF, Module.Basis.ofIsLocalizedModule_apply, hv]
  obtain ⟨_, hfreeF⟩ := exists_smul_ιMulti_and_smul_injective d bF
  rw [hbF] at hfreeF

  have hω' : topFormMap K K A F d ω = algebraMap A F c • exteriorPower.ιMulti F d v := by
    rw [hc, LinearMap.map_smul, hρ, algebraMap_smul]
  rw [hω']
  intro h0
  have := hfreeF _ 0 (by rw [h0, zero_smul])
  exact (hcU.map (algebraMap A F)).ne_zero this

end P2mFrameNZ

theorem solution
    (K A F : Type u) [Field K] [CommRing A] [Algebra K A] [Field F] [Algebra A F] [Algebra K F]
    [IsScalarTower K A F] (M : Submonoid A) [IsLocalization M F]
    (d : ℕ) (b : Module.Basis (Fin d) A (Ω[A⁄K]))
    (ω : ⋀[A]^d (Ω[A⁄K])) (hω : Function.Bijective fun g : A => g • ω) :
    NeronModelInfra.TopFormOrder.topFormMap K K A F d ω ≠ 0 :=
  P2mFrameNZ.main K A F M d b ω hω

end S_NeronModelInfra_TopFormOrder_topFormMap_ne_zero_of_bijective_smul_of_isLocalization
end P2MW
export P2MW.S_NeronModelInfra_TopFormOrder_topFormMap_ne_zero_of_bijective_smul_of_isLocalization (solution)
