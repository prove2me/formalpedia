-- Prove2me | solution 1 for ModularCurve.XHDRModelAtP.eq_comap_or_eq_comap_of_mem_minimalPrimes_natCast_of_specializes
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/053c6cd5-a86a-5b82-b28a-366d434f1ea8

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtPCrossingFrame
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XHDRModelAtP_eq_comap_or_eq_comap_of_mem_minimalPrimes_natCast_of_specializes

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ModularCurve ModularCurve.XHDRLevel
open scoped MatrixGroups

namespace Ideal p2m_export "Ideal" "height height_mono IsPrime.ne_top mem_bot span isPrime_bot mem_minimalPrimes_of_height_eq span_singleton_eq_bot comap_isPrime eq_top_of_isUnit_mem one_le_height_span_singleton_of_mem_nonZeroDivisors map span_singleton_le_iff_mem height_le_one_of_isPrincipal_of_mem_minimalPrimes ext IsPrime.ne_top' IsPrime ResidueField mem_comap under comap height_span_singleton_eq_one_of_mem_nonZeroDivisors" end Ideal
p2m_open_scoped "Ideal" in

private theorem Ideal.height_eq_one_iff_mem_minimalPrimes_span_singleton_of_mem
    {R : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    {x : R} (hx : x ≠ 0) (P : Ideal R) [P.IsPrime] (hxP : x ∈ P) :
    P.height = 1 ↔ P ∈ (Ideal.span {x}).minimalPrimes := by
  have hle : Ideal.span {x} ≤ P := (Ideal.span_singleton_le_iff_mem _).mpr hxP
  have hx' : x ∈ nonZeroDivisors R := mem_nonZeroDivisors_of_ne_zero hx
  have hxu : ¬ IsUnit x := fun hu => Ideal.IsPrime.ne_top' (Ideal.eq_top_of_isUnit_mem P hxP hu)
  have hspan : (Ideal.span {x}).height = 1 := Ideal.height_span_singleton_eq_one_of_mem_nonZeroDivisors hx' hxu
  constructor
  · intro hP
    exact Ideal.mem_minimalPrimes_of_height_eq hle (by rw [hP, hspan])
  · intro hP
    apply le_antisymm
    · exact Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes (Ideal.span {x}) P hP
    · exact hspan ▸ Ideal.height_mono hle

p2m_open_scoped "Ideal" in

private theorem Ideal.eq_of_mem_minimalPrimes_span_singleton_of_le
    {R : Type*} [CommRing R] {x : R} {P : Ideal R} (hP : P ∈ (Ideal.span {x}).minimalPrimes)
    (Q : Ideal R) [Q.IsPrime] (hxQ : x ∈ Q) (hQP : Q ≤ P) : Q = P :=
  le_antisymm hQP (hP.2 ⟨‹Q.IsPrime›, (Ideal.span_singleton_le_iff_mem _).mpr hxQ⟩ hQP)

theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (IsLocalRing.ResidueField ↥A) p] [IsAlgClosed (IsLocalRing.ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))
    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ρO : R p →+* O)
    (hϖ : IsLocalRing.maximalIdeal O = Ideal.span {((p : ℕ) : O)})
    [hint : IsIntegral (XO (ΓM M H) hj ρO)]
    (toκ : O →+* IsLocalRing.ResidueField ↥A) (htoκ : toκ.comp ρO = (IsLocalRing.residue ↥A).comp ρ)
    (x : ↥(XO (ΓM M H) hj ρO)) [IsNoetherianRing ((XO (ΓM M H) hj ρO).presheaf.stalk x)]
    (hsp₁ : 𝔛.ξinf A hA ρ hρ ρO toκ htoκ ⤳ x) (hsp₂ : 𝔛.ξzero A hA ρ hρ ρO toκ htoκ ⤳ x) :
    (Ideal.comap ((XO (ΓM M H) hj ρO).presheaf.stalkSpecializes hsp₁).hom (IsLocalRing.maximalIdeal _)).IsPrime ∧
    ((p : ℕ) : (XO (ΓM M H) hj ρO).presheaf.stalk x) ∈ Ideal.comap ((XO (ΓM M H) hj ρO).presheaf.stalkSpecializes hsp₁).hom (IsLocalRing.maximalIdeal _) ∧
    (Ideal.comap ((XO (ΓM M H) hj ρO).presheaf.stalkSpecializes hsp₂).hom (IsLocalRing.maximalIdeal _)).IsPrime ∧
    ((p : ℕ) : (XO (ΓM M H) hj ρO).presheaf.stalk x) ∈ Ideal.comap ((XO (ΓM M H) hj ρO).presheaf.stalkSpecializes hsp₂).hom (IsLocalRing.maximalIdeal _) ∧
    (∀ 𝔭 : Ideal ((XO (ΓM M H) hj ρO).presheaf.stalk x), 𝔭 ∈ (Ideal.span {((p : ℕ) : (XO (ΓM M H) hj ρO).presheaf.stalk x)}).minimalPrimes →
      𝔭 = Ideal.comap ((XO (ΓM M H) hj ρO).presheaf.stalkSpecializes hsp₁).hom (IsLocalRing.maximalIdeal _) ∨ 𝔭 = Ideal.comap ((XO (ΓM M H) hj ρO).presheaf.stalkSpecializes hsp₂).hom (IsLocalRing.maximalIdeal _)) ∧
    (∀ (𝔭 : Ideal ((XO (ΓM M H) hj ρO).presheaf.stalk x)) [𝔭.IsPrime], 𝔭.height = 1 → ((p : ℕ) : (XO (ΓM M H) hj ρO).presheaf.stalk x) ∈ 𝔭 →
      𝔭 = Ideal.comap ((XO (ΓM M H) hj ρO).presheaf.stalkSpecializes hsp₁).hom (IsLocalRing.maximalIdeal _) ∨ 𝔭 = Ideal.comap ((XO (ΓM M H) hj ρO).presheaf.stalkSpecializes hsp₂).hom (IsLocalRing.maximalIdeal _)) := by
  classical
  haveI := (𝔛.Mfib A hA ρ hρ).isIntegral

  have hOpt : ∀ (𝔮 : Ideal O) [𝔮.IsPrime], ((p : ℕ) : O) ∈ 𝔮 → 𝔮 = IsLocalRing.maximalIdeal O := by
    intro 𝔮 _ hq
    have hle : IsLocalRing.maximalIdeal O ≤ 𝔮 := by
      rw [hϖ, Ideal.span_singleton_le_iff_mem]; exact hq
    exact ((IsLocalRing.maximalIdeal.isMaximal O).eq_of_le (Ideal.IsPrime.ne_top ‹_›) hle).symm

  have hfib : ∀ z : ↥(XO (ΓM M H) hj ρO), ¬ IsUnit ((p : ℕ) : (XO (ΓM M H) hj ρO).presheaf.stalk z) →
      (XO.toBase (ΓM M H) hj ρO).base z = IsLocalRing.closedPoint O := by
    intro z hz
    set s := (XO.toBase (ΓM M H) hj ρO) with hs

    have h1 : ¬ IsUnit ((p : ℕ) : (Spec (CommRingCat.of O)).presheaf.stalk (s.base z)) := by
      intro hu
      apply hz
      have := hu.map (s.stalkMap z).hom
      rwa [map_natCast] at this

    letI := StructureSheaf.stalkAlgebra (↑(CommRingCat.of O)) (s.base z)
    haveI := StructureSheaf.IsLocalization.to_stalk (↑(CommRingCat.of O)) (s.base z)
    have h2 : ((p : ℕ) : O) ∈ (s.base z).asIdeal := by
      by_contra hn
      apply h1
      have := (IsLocalization.AtPrime.isUnit_to_map_iff
        ((Spec.structureSheaf ↑(CommRingCat.of O)).presheaf.stalk (s.base z)) (s.base z).asIdeal ((p : ℕ) : O)).mpr hn
      rwa [map_natCast] at this
    apply PrimeSpectrum.ext
    exact hOpt _ h2

  have hker : RingHom.ker toκ = IsLocalRing.maximalIdeal O := by
    haveI : (RingHom.ker toκ).IsPrime := RingHom.ker_isPrime toκ
    exact hOpt _ (by rw [RingHom.mem_ker, map_natCast, CharP.cast_eq_zero])
  have hrange : ∀ z : ↥(XO (ΓM M H) hj ρO),
      (XO.toBase (ΓM M H) hj ρO).base z = IsLocalRing.closedPoint O →
      ∃ z' : ↥(fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ)), (bcMap (ΓM M H) hj ρO toκ htoκ).base z' = z := by
    intro z hz
    have hz' : z ∈ Set.range ⇑(bcMap (ΓM M H) hj ρO toκ htoκ).base := by
      rw [bcMap, Scheme.Pullback.range_map]
      refine ⟨by simp, ?_⟩
      show (XO.toBase (ΓM M H) hj ρO).base z ∈ Set.range (Spec.map (CommRingCat.ofHom toκ)).base
      refine ⟨IsLocalRing.closedPoint (IsLocalRing.ResidueField ↥A), ?_⟩
      rw [hz]
      apply PrimeSpectrum.ext
      change Ideal.comap toκ (IsLocalRing.closedPoint (IsLocalRing.ResidueField ↥A)).asIdeal = (IsLocalRing.closedPoint O).asIdeal
      rw [show (IsLocalRing.closedPoint (IsLocalRing.ResidueField ↥A)).asIdeal = ⊥ from IsLocalRing.maximalIdeal_eq_bot (R := (IsLocalRing.ResidueField ↥A)) |>.symm ▸ rfl,
        ← RingHom.ker_eq_comap_bot, hker]
      rfl
    obtain ⟨z', hz''⟩ := hz'
    exact ⟨z', hz''⟩

  have hbranch : ∀ z' : ↥(fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ)),
      𝔛.ξinf A hA ρ hρ ρO toκ htoκ ⤳ (bcMap (ΓM M H) hj ρO toκ htoκ).base z' ∨
      𝔛.ξzero A hA ρ hρ ρO toκ htoκ ⤳ (bcMap (ΓM M H) hj ρO toκ htoκ).base z' := by
    intro z'
    rcases 𝔛.comp_jointly_surjective A hA ρ hρ z' with ⟨c, rfl⟩ | ⟨c, rfl⟩
    · left
      rw [← Scheme.Hom.comp_apply]
      exact (𝔛.efib_genericPoint_specializes A hA ρ hρ c).map (Scheme.Hom.continuous _)
    · right
      rw [← Scheme.Hom.comp_apply]
      exact (𝔛.efib_genericPoint_specializes A hA ρ hρ c).map (Scheme.Hom.continuous _)

  have hpk : ∀ z' : ↥(fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ)), ¬ IsUnit ((p : ℕ) : (XO (ΓM M H) hj ρO).presheaf.stalk ((bcMap (ΓM M H) hj ρO toκ htoκ).base z')) := by
    intro z' hu

    have h0 : ((p : ℕ) : (fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ)).presheaf.stalk z') = 0 := by
      let ψ : (IsLocalRing.ResidueField ↥A) →+* (fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ)).presheaf.stalk z' :=
        ((fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ)).presheaf.germ ⊤ z' trivial).hom.comp
          ((pullback.snd (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)))).appTop.hom.comp
            (Scheme.ΓSpecIso (CommRingCat.of (IsLocalRing.ResidueField ↥A))).inv.hom)
      rw [← map_natCast ψ, CharP.cast_eq_zero, map_zero]
    have := hu.map ((bcMap (ΓM M H) hj ρO toκ htoκ).stalkMap z').hom
    rw [map_natCast, h0] at this
    exact not_isUnit_zero this
  have hmem₁ : ((p : ℕ) : (XO (ΓM M H) hj ρO).presheaf.stalk x) ∈
      Ideal.comap ((XO (ΓM M H) hj ρO).presheaf.stalkSpecializes hsp₁).hom (IsLocalRing.maximalIdeal _) := by
    rw [Ideal.mem_comap, map_natCast, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    exact hpk _
  have hmem₂ : ((p : ℕ) : (XO (ΓM M H) hj ρO).presheaf.stalk x) ∈
      Ideal.comap ((XO (ΓM M H) hj ρO).presheaf.stalkSpecializes hsp₂).hom (IsLocalRing.maximalIdeal _) := by
    rw [Ideal.mem_comap, map_natCast, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    exact hpk _

  have hconv : ∀ (𝔭 : Ideal ((XO (ΓM M H) hj ρO).presheaf.stalk x)), 𝔭 ∈ (Ideal.span {((p : ℕ) : (XO (ΓM M H) hj ρO).presheaf.stalk x)}).minimalPrimes →
      𝔭 = Ideal.comap ((XO (ΓM M H) hj ρO).presheaf.stalkSpecializes hsp₁).hom (IsLocalRing.maximalIdeal _) ∨
      𝔭 = Ideal.comap ((XO (ΓM M H) hj ρO).presheaf.stalkSpecializes hsp₂).hom (IsLocalRing.maximalIdeal _) := by
    intro 𝔭 h𝔭
    haveI h𝔭p : 𝔭.IsPrime := h𝔭.1.1
    have hp𝔭 : ((p : ℕ) : (XO (ΓM M H) hj ρO).presheaf.stalk x) ∈ 𝔭 := (Ideal.span_singleton_le_iff_mem _).mp h𝔭.1.2

    let q𝔭 : Spec ((XO (ΓM M H) hj ρO).presheaf.stalk x) := ⟨𝔭, h𝔭p⟩
    let F := (XO (ΓM M H) hj ρO).fromSpecStalk x

    have hy : ¬ IsUnit ((p : ℕ) : (XO (ΓM M H) hj ρO).presheaf.stalk (F.base q𝔭)) := by
      intro hu
      letI := StructureSheaf.stalkAlgebra (↑((XO (ΓM M H) hj ρO).presheaf.stalk x)) q𝔭
      haveI := StructureSheaf.IsLocalization.to_stalk (↑((XO (ΓM M H) hj ρO).presheaf.stalk x)) q𝔭
      have := hu.map (F.stalkMap q𝔭).hom
      rw [map_natCast] at this
      have h2 := (IsLocalization.AtPrime.isUnit_to_map_iff
        ((Spec.structureSheaf ↑((XO (ΓM M H) hj ρO).presheaf.stalk x)).presheaf.stalk q𝔭) q𝔭.asIdeal ((p : ℕ) : (XO (ΓM M H) hj ρO).presheaf.stalk x)).mp
        (by rwa [map_natCast])
      exact h2 hp𝔭

    obtain ⟨z', hz'⟩ := hrange _ (hfib _ hy)
    have hbr := hbranch z'
    rw [hz'] at hbr

    have key : ∀ {η : ↥(XO (ΓM M H) hj ρO)} (hη : η ⤳ x), ¬ IsUnit ((p : ℕ) : (XO (ΓM M H) hj ρO).presheaf.stalk η) → η ⤳ F.base q𝔭 →
        𝔭 = Ideal.comap ((XO (ΓM M H) hj ρO).presheaf.stalkSpecializes hη).hom (IsLocalRing.maximalIdeal _) := by
      intro η hη hpη hsp
      let qη : Spec ((XO (ΓM M H) hj ρO).presheaf.stalk x) :=
        (Spec.map ((XO (ΓM M H) hj ρO).presheaf.stalkSpecializes hη)).base (IsLocalRing.closedPoint _)
      have hFq : F.base qη = η := by
        show (Spec.map ((XO (ΓM M H) hj ρO).presheaf.stalkSpecializes hη) ≫ (XO (ΓM M H) hj ρO).fromSpecStalk x).base (IsLocalRing.closedPoint _) = η
        rw [Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
        exact Scheme.fromSpecStalk_closedPoint
      rw [← hFq] at hsp
      have hsp' : qη ⤳ q𝔭 := (F.isEmbedding.isInducing.specializes_iff).mp hsp
      have hle : qη.asIdeal ≤ 𝔭 := (PrimeSpectrum.le_iff_specializes qη q𝔭).mpr hsp'
      have hmem : ((p : ℕ) : (XO (ΓM M H) hj ρO).presheaf.stalk x) ∈ qη.asIdeal := by
        change _ ∈ Ideal.comap _ _
        rw [Ideal.mem_comap, map_natCast]
        show _ ∈ IsLocalRing.maximalIdeal _
        rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
        exact hpη
      exact (Ideal.eq_of_mem_minimalPrimes_span_singleton_of_le h𝔭 qη.asIdeal hmem hle).symm
    rcases hbr with h | h
    · exact Or.inl (key hsp₁ (hpk _) h)
    · exact Or.inr (key hsp₂ (hpk _) h)

  have hp0 : ((p : ℕ) : (XO (ΓM M H) hj ρO).presheaf.stalk x) ≠ 0 := by
    intro h0

    have hxunit : ¬ IsUnit ((p : ℕ) : (XO (ΓM M H) hj ρO).presheaf.stalk x) := by rw [h0]; exact not_isUnit_zero
    have hx := hfib x hxunit

    haveI := 𝔛.flat
    haveI : Flat (XO.toBase (ΓM M H) hj ρO) := inferInstance
    have hgen := Flat.generalizingMap (XO.toBase (ΓM M H) hj ρO)
    let ξ : Spec (CommRingCat.of O) := ⟨⊥, Ideal.isPrime_bot⟩
    have hξ : ξ ⤳ (XO.toBase (ΓM M H) hj ρO).base x := by
      rw [hx]
      exact (PrimeSpectrum.le_iff_specializes ξ (IsLocalRing.closedPoint O)).mp bot_le
    obtain ⟨x', hx'x, hx'⟩ := hgen hξ

    have hp' : IsUnit ((p : ℕ) : (XO (ΓM M H) hj ρO).presheaf.stalk x') := by
      have hpO : ((p : ℕ) : O) ≠ 0 := by
        intro h
        apply IsDiscreteValuationRing.not_a_field O
        rw [hϖ, h, Ideal.span_singleton_eq_bot.mpr rfl]
      letI := StructureSheaf.stalkAlgebra (↑(CommRingCat.of O)) ξ
      haveI := StructureSheaf.IsLocalization.to_stalk (↑(CommRingCat.of O)) ξ
      have hu : IsUnit ((p : ℕ) : (Spec (CommRingCat.of O)).presheaf.stalk ξ) := by
        have := (IsLocalization.AtPrime.isUnit_to_map_iff
          ((Spec.structureSheaf ↑(CommRingCat.of O)).presheaf.stalk ξ) ξ.asIdeal ((p : ℕ) : O)).mpr
          (by show ((p : ℕ) : O) ∉ (⊥ : Ideal O); rwa [Ideal.mem_bot])
        rwa [map_natCast] at this
      have hx'eq : (XO.toBase (ΓM M H) hj ρO).base x' = ξ := hx'
      have := hu
      rw [← hx'eq] at this
      have h2 := this.map ((XO.toBase (ΓM M H) hj ρO).stalkMap x').hom
      rwa [map_natCast] at h2
    have h3 := congrArg ((XO (ΓM M H) hj ρO).presheaf.stalkSpecializes hx'x).hom h0
    rw [map_natCast, map_zero] at h3
    rw [h3] at hp'
    exact not_isUnit_zero hp'

  refine ⟨Ideal.comap_isPrime _ _, hmem₁, Ideal.comap_isPrime _ _, hmem₂, hconv, ?_⟩
  intro 𝔭 _ hht hp𝔭
  exact hconv 𝔭 ((Ideal.height_eq_one_iff_mem_minimalPrimes_span_singleton_of_mem hp0 𝔭 hp𝔭).mp hht)

end S_ModularCurve_XHDRModelAtP_eq_comap_or_eq_comap_of_mem_minimalPrimes_natCast_of_specializes
end P2MW
export P2MW.S_ModularCurve_XHDRModelAtP_eq_comap_or_eq_comap_of_mem_minimalPrimes_natCast_of_specializes (solution)
