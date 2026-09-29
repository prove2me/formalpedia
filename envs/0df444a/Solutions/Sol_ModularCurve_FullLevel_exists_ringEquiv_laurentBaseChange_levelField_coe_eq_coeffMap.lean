-- Prove2me | solution 1 for ModularCurve.FullLevel.exists_ringEquiv_laurentBaseChange_levelField_coe_eq_coeffMap
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.339302+00:00
-- url     : https://prove2.me/submissions/f671000d-23ac-5e87-b705-35c7e5e158e9

import Definitions.Def_ModularCurve_FullLevelSemistableCovering
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_ModularCurve_XH
import Definitions.Def_ModularCurve_LaurentCoeff
import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_exists_ringEquiv_laurentBaseChange_levelField_coe_eq_coeffMap

set_option autoImplicit false

open ModularCurve ModularCurve.FullLevel

namespace FTAux

theorem exists_linearIndependent_regroup {K Ω Φ : Type*} [Field K] [Field Ω] [Algebra K Ω]
    [CommRing Φ] [Algebra Ω Φ] {n : ℕ} (v : Fin n → Ω) :
    ∃ (t : ℕ) (e : Fin t → Ω) (r : Fin n → Fin t → K), LinearIndependent K e ∧
      ∀ w : Fin n → Φ, ∑ i, algebraMap Ω Φ (v i) * w i =
        ∑ k, algebraMap Ω Φ (e k) * ∑ i, algebraMap Ω Φ (algebraMap K Ω (r i k)) * w i := by
  classical
  let W : Submodule K Ω := Submodule.span K (Set.range v)
  haveI : Module.Finite K W := Module.Finite.span_of_finite K (Set.finite_range v)
  let b := Module.finBasis K W
  have hvW : ∀ i, v i ∈ W := fun i => Submodule.subset_span ⟨i, rfl⟩
  refine ⟨Module.finrank K W, fun k => (b k : Ω), fun i k => b.repr ⟨v i, hvW i⟩ k, ?_, ?_⟩
  · have h := b.linearIndependent.map' W.subtype (Submodule.ker_subtype W)
    exact h
  · intro w
    have hv : ∀ i, v i = ∑ k, algebraMap K Ω (b.repr ⟨v i, hvW i⟩ k) * (b k : Ω) := by
      intro i
      have h := congrArg W.subtype (b.sum_repr ⟨v i, hvW i⟩)
      rw [map_sum] at h
      simp only [map_smul, Submodule.subtype_apply, Algebra.smul_def] at h
      exact h.symm
    have step : ∀ i, algebraMap Ω Φ (v i) * w i =
        ∑ k, algebraMap Ω Φ (b k : Ω) * (algebraMap Ω Φ (algebraMap K Ω (b.repr ⟨v i, hvW i⟩ k)) * w i) := by
      intro i
      conv_lhs => rw [hv i, map_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [map_mul]
      ring
    rw [Finset.sum_congr rfl (fun i _ => step i), Finset.sum_comm]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [Finset.mul_sum]

end FTAux

set_option maxHeartbeats 4000000 in
theorem solution
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M']
    (k₀ : IntermediateField ℚ (AlgebraicClosure ℚ))
    (K₁ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) (hK₁ : FiniteDimensional ↥k₀ ↥K₁) :
    letI : Algebra ↥k₀ ↥(fieldBar q M') :=
      ((algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')).comp (algebraMap ↥k₀ (AlgebraicClosure ℚ))).toAlgebra
    ∀ (F₀ : IntermediateField ↥k₀ ↥(fieldBar q M')),

      IntermediateField.adjoin ↥k₀ (Set.range (algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M'))) ⊔ F₀ = ⊤ →

      (∀ (m : ℕ) (c : Fin m → AlgebraicClosure ℚ) (a : Fin m → ↥(fieldBar q M')), (∀ i, a i ∈ IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) →
          LinearIndependent ↥K₁ c → ∑ i, algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') (c i) * a i = 0 → ∀ i, a i = 0) →

      (∀ f : ↥(fieldBar q M'), (f : LaurentSeries (AlgebraicClosure ℚ)) ∈ Set.range ⇑(coeffEmb (AlgebraicClosure ℚ)) → f ∈ F₀) →
      ∃ e : ↥(laurentBaseChange ↥K₁ (xHFunctionField (q ^ 2 * M') (levelH q M'))) ≃+*
          ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀),
        ∀ f : ↥(laurentBaseChange ↥K₁ (xHFunctionField (q ^ 2 * M') (levelH q M'))),
          (((e f : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)) :
              ↥(fieldBar q M')) : LaurentSeries (AlgebraicClosure ℚ)) =
            coeffMap (algebraMap ↥K₁ (AlgebraicClosure ℚ)) (f : LaurentSeries ↥K₁) := by
  classical
  letI instAlg : Algebra ↥k₀ ↥(fieldBar q M') :=
    ((algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')).comp (algebraMap ↥k₀ (AlgebraicClosure ℚ))).toAlgebra
  intro F₀ hK1 hLD hRAT

  let Ω := AlgebraicClosure ℚ
  let ι : ↥K₁ →+* Ω := algebraMap ↥K₁ Ω
  let ρ : Ω →+* ↥(fieldBar q M') := algebraMap Ω ↥(fieldBar q M')
  let FH : IntermediateField ℚ (LaurentSeries ℚ) := xHFunctionField (q ^ 2 * M') (levelH q M')
  let B : IntermediateField ↥K₁ (LaurentSeries ↥K₁) := laurentBaseChange ↥K₁ FH
  let T : IntermediateField ↥k₀ ↥(fieldBar q M') :=
    IntermediateField.adjoin ↥k₀ (⇑ρ '' (↑K₁ : Set Ω)) ⊔ F₀
  have hTconst : ∀ c : ↥K₁, ρ (ι c) ∈ T := fun c =>
    le_sup_left (b := F₀) (IntermediateField.subset_adjoin ↥k₀ _ ⟨(c : Ω), c.2, rfl⟩)
  have hTF₀ : ∀ f : ↥(fieldBar q M'), f ∈ F₀ → f ∈ T := fun f hf =>
    le_sup_right (a := IntermediateField.adjoin ↥k₀ (⇑ρ '' (↑K₁ : Set Ω))) hf

  have hconst : ∀ c : ↥K₁, coeffMap ι (algebraMap ↥K₁ (LaurentSeries ↥K₁) c) =
      algebraMap Ω (LaurentSeries Ω) (ι c) := by
    intro c
    rw [algebraMap_laurentSeries_eq_single, algebraMap_laurentSeries_eq_single, coeffMap_single]
  have hemb : ∀ z : LaurentSeries ℚ, coeffMap ι (coeffEmb ↥K₁ z) = coeffEmb Ω z := by
    intro z
    show coeffMap ι (coeffMap (algebraMap ℚ ↥K₁) z) = coeffMap (algebraMap ℚ Ω) z
    rw [coeffMap_coeffMap]
    exact coeffMap_congr (Subsingleton.elim _ _) z

  have hBT : ∀ x : LaurentSeries ↥K₁, x ∈ B →
      ∃ t : ↥(fieldBar q M'), t ∈ T ∧ (t : LaurentSeries Ω) = coeffMap ι x := by
    intro x hx
    rw [mem_laurentBaseChange_iff] at hx
    have hle : Subfield.closure (Set.range (algebraMap ↥K₁ (LaurentSeries ↥K₁)) ∪
        (⇑(coeffEmb ↥K₁) '' (FH : Set (LaurentSeries ℚ)))) ≤
        (T.toSubfield.map (algebraMap ↥(fieldBar q M') (LaurentSeries Ω))).comap (coeffMap ι) := by
      rw [Subfield.closure_le]
      rintro y (⟨c, rfl⟩ | ⟨z, hz, rfl⟩)
      · refine Subfield.mem_comap.2 ⟨ρ (ι c), hTconst c, ?_⟩
        rw [hconst]; rfl
      · refine Subfield.mem_comap.2 ⟨⟨coeffEmb Ω z, coeffEmb_mem_laurentBaseChange Ω hz⟩, ?_, ?_⟩
        · exact hTF₀ _ (hRAT _ ⟨z, rfl⟩)
        · rw [hemb]; rfl
    obtain ⟨t, ht, htx⟩ := Subfield.mem_map.1 (hle hx)
    exact ⟨t, ht, htx⟩

  have hmemFb : ∀ x : ↥B, ((coeffMap ι).comp (algebraMap ↥B (LaurentSeries ↥K₁))) x ∈ fieldBar q M' := by
    intro x
    obtain ⟨t, -, ht⟩ := hBT x.1 x.2
    show coeffMap ι (x : LaurentSeries ↥K₁) ∈ fieldBar q M'
    rw [← ht]; exact t.2
  let ψ₀ : ↥B →+* ↥(fieldBar q M') :=
    RingHom.codRestrict ((coeffMap ι).comp (algebraMap ↥B (LaurentSeries ↥K₁))) (fieldBar q M') hmemFb
  have hψ₀ : ∀ x : ↥B, ((ψ₀ x : ↥(fieldBar q M')) : LaurentSeries Ω) = coeffMap ι (x : LaurentSeries ↥K₁) :=
    fun x => rfl
  have hmemT : ∀ x : ↥B, ψ₀ x ∈ T := by
    intro x
    obtain ⟨t, htT, ht⟩ := hBT x.1 x.2
    have : t = ψ₀ x := Subtype.ext (by rw [hψ₀, ht])
    rw [← this]; exact htT
  let ψ : ↥B →+* ↥T := RingHom.codRestrict ψ₀ T hmemT
  have hψ : ∀ x : ↥B, (((ψ x : ↥T) : ↥(fieldBar q M')) : LaurentSeries Ω) = coeffMap ι (x : LaurentSeries ↥K₁) :=
    fun x => rfl
  have hinj : Function.Injective ψ := ψ.injective

  let R : Subfield ↥(fieldBar q M') := ψ₀.fieldRange
  have hRconst : ∀ c : ↥K₁, ρ (ι c) ∈ R := by
    intro c
    refine ⟨⟨algebraMap ↥K₁ (LaurentSeries ↥K₁) c, B.algebraMap_mem c⟩, Subtype.ext ?_⟩
    rw [hψ₀]
    exact hconst c
  have hRemb : ∀ (z : LaurentSeries ℚ) (hz : z ∈ FH),
      (⟨coeffEmb Ω z, coeffEmb_mem_laurentBaseChange Ω hz⟩ : ↥(fieldBar q M')) ∈ R := by
    intro z hz
    refine ⟨⟨coeffEmb ↥K₁ z, coeffEmb_mem_laurentBaseChange ↥K₁ hz⟩, Subtype.ext ?_⟩
    rw [hψ₀]
    exact hemb z

  have hspan : ∀ y : LaurentSeries Ω, y ∈ Algebra.adjoin Ω (⇑(coeffEmb Ω) '' (FH : Set (LaurentSeries ℚ))) →
      ∃ (n : ℕ) (c : Fin n → Ω) (g : Fin n → LaurentSeries ℚ), (∀ i, g i ∈ FH) ∧
        ∑ i, algebraMap Ω (LaurentSeries Ω) (c i) * coeffEmb Ω (g i) = y := by
    intro y hy
    let Smon : Submonoid (LaurentSeries Ω) :=
      (FH.toSubalgebra.toSubsemiring.toSubmonoid).map (coeffEmb Ω : LaurentSeries ℚ →+* LaurentSeries Ω).toMonoidHom
    have hS : (⇑(coeffEmb Ω) '' (FH : Set (LaurentSeries ℚ))) = (Smon : Set (LaurentSeries Ω)) := rfl
    have h := Algebra.adjoin_eq_span Ω (⇑(coeffEmb Ω) '' (FH : Set (LaurentSeries ℚ)))
    rw [hS, Submonoid.closure_eq, ← hS] at h
    have hy2 := h.le ((Subalgebra.mem_toSubmodule _).2 hy)
    obtain ⟨n, c, g, hsum⟩ :=
      (@Submodule.mem_span_set' Ω (LaurentSeries Ω) _ _ (Algebra.toModule) y _).1 hy2
    simp only [Algebra.smul_def] at hsum
    have hg2 : ∀ i, ∃ z, z ∈ FH ∧ coeffEmb Ω z = (g i : LaurentSeries Ω) := fun i => (g i).2
    choose g' hg'1 hg'2 using hg2
    refine ⟨n, c, g', hg'1, ?_⟩
    rw [← hsum]
    exact Finset.sum_congr rfl (fun i _ => by rw [hg'2])

  have hF₀R : ∀ f : ↥(fieldBar q M'), f ∈ F₀ → f ∈ R := by
    intro f hf
    have hfadj : (f : LaurentSeries Ω) ∈
        IntermediateField.adjoin Ω (⇑(coeffEmb Ω) '' (FH : Set (LaurentSeries ℚ))) := f.2
    obtain ⟨r, hr, s, hs, hrs⟩ := IntermediateField.mem_adjoin_iff_div.1 hfadj
    obtain ⟨nr, c, g, hg, hr'⟩ := hspan r hr
    obtain ⟨ns, d, h, hh, hs'⟩ := hspan s hs

    let G : Fin nr → ↥(fieldBar q M') := fun i => ⟨coeffEmb Ω (g i), coeffEmb_mem_laurentBaseChange Ω (hg i)⟩
    let H : Fin ns → ↥(fieldBar q M') := fun j => ⟨coeffEmb Ω (h j), coeffEmb_mem_laurentBaseChange Ω (hh j)⟩
    have hGR : ∀ i, G i ∈ R := fun i => hRemb _ (hg i)
    have hHR : ∀ j, H j ∈ R := fun j => hRemb _ (hh j)
    have hGF₀ : ∀ i, G i ∈ F₀ := fun i => hRAT _ ⟨g i, rfl⟩
    have hHF₀ : ∀ j, H j ∈ F₀ := fun j => hRAT _ ⟨h j, rfl⟩

    let Rf : ↥(fieldBar q M') := ∑ i, ρ (c i) * G i
    let Sf : ↥(fieldBar q M') := ∑ j, ρ (d j) * H j
    have hRval : (Rf : LaurentSeries Ω) = r := by
      rw [← hr']
      show ((∑ i, ρ (c i) * G i : ↥(fieldBar q M')) : LaurentSeries Ω) = _
      rw [IntermediateField.coe_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [IntermediateField.coe_mul]
      rfl
    have hSval : (Sf : LaurentSeries Ω) = s := by
      rw [← hs']
      show ((∑ j, ρ (d j) * H j : ↥(fieldBar q M')) : LaurentSeries Ω) = _
      rw [IntermediateField.coe_sum]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [IntermediateField.coe_mul]
      rfl
    by_cases hs0 : s = 0
    · have hf0 : f = 0 := Subtype.ext (by rw [hrs, hs0, div_zero]; rfl)
      rw [hf0]; exact R.zero_mem
    have hfs : (f : LaurentSeries Ω) * s = r := by rw [hrs, div_mul_cancel₀ r hs0]
    have hrel : f * Sf = Rf := Subtype.ext (by rw [IntermediateField.coe_mul, hSval, hRval, hfs])
    have hS0 : Sf ≠ 0 := fun h0 => hs0 (by rw [← hSval, h0]; rfl)

    let v : Fin (ns + nr) → Ω := Fin.addCases d c
    let a : Fin (ns + nr) → ↥(fieldBar q M') := Fin.addCases (fun j => f * H j) (fun i => -G i)
    have haT : ∀ idx, a idx ∈ T := by
      intro idx
      refine Fin.addCases (fun j => ?_) (fun i => ?_) idx
      · show a (Fin.castAdd nr j) ∈ T
        simp only [a, Fin.addCases_left]
        exact mul_mem (hTF₀ f hf) (hTF₀ _ (hHF₀ j))
      · show a (Fin.natAdd ns i) ∈ T
        simp only [a, Fin.addCases_right]
        exact neg_mem (hTF₀ _ (hGF₀ i))
    have hva : ∑ idx, ρ (v idx) * a idx = 0 := by
      rw [Fin.sum_univ_add]
      simp only [v, a, Fin.addCases_left, Fin.addCases_right]
      have h1 : ∑ j, ρ (d j) * (f * H j) = f * Sf := by
        simp only [Sf, Finset.mul_sum]
        exact Finset.sum_congr rfl (fun j _ => by ring)
      have h2 : ∑ i, ρ (c i) * -G i = -Rf := by
        simp only [Rf, ← Finset.sum_neg_distrib]
        exact Finset.sum_congr rfl (fun i _ => by ring)
      rw [h1, h2, hrel, add_neg_cancel]

    obtain ⟨t, e, rr, he, hregroup⟩ :=
      FTAux.exists_linearIndependent_regroup (K := ↥K₁) (Φ := ↥(fieldBar q M')) v
    have hA0 : ∀ k, ∑ idx, ρ (ι (rr idx k)) * a idx = 0 := by
      have hreg := hregroup a
      rw [hva] at hreg
      exact hLD t e (fun k => ∑ idx, ρ (ι (rr idx k)) * a idx)
        (fun k => sum_mem (fun idx _ => mul_mem (hTconst _) (haT idx))) he hreg.symm

    let D : Fin t → ↥(fieldBar q M') := fun k => ∑ j, ρ (ι (rr (Fin.castAdd nr j) k)) * H j
    let N : Fin t → ↥(fieldBar q M') := fun k => ∑ i, ρ (ι (rr (Fin.natAdd ns i) k)) * G i
    have hDN : ∀ k, f * D k = N k := by
      intro k
      have hk := hA0 k
      rw [Fin.sum_univ_add] at hk
      simp only [a, Fin.addCases_left, Fin.addCases_right] at hk
      have h1 : ∑ j, ρ (ι (rr (Fin.castAdd nr j) k)) * (f * H j) = f * D k := by
        simp only [D, Finset.mul_sum]
        exact Finset.sum_congr rfl (fun j _ => by ring)
      have h2 : ∑ i, ρ (ι (rr (Fin.natAdd ns i) k)) * -G i = -N k := by
        simp only [N, ← Finset.sum_neg_distrib]
        exact Finset.sum_congr rfl (fun i _ => by ring)
      rw [h1, h2, add_neg_eq_zero] at hk
      exact hk
    have hSD : Sf = ∑ k, ρ (e k) * D k := by
      have hreg := hregroup (Fin.addCases H (fun _ => 0))
      rw [Fin.sum_univ_add] at hreg
      simp only [v, Fin.addCases_left, Fin.addCases_right, mul_zero, Finset.sum_const_zero,
        add_zero] at hreg
      rw [show Sf = ∑ j, ρ (d j) * H j from rfl, hreg]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      congr 1
      rw [Fin.sum_univ_add]
      simp only [Fin.addCases_left, Fin.addCases_right, mul_zero, Finset.sum_const_zero, add_zero]
      rfl
    have hDk : ∃ k, D k ≠ 0 := by
      by_contra hall
      push Not at hall
      apply hS0
      rw [hSD]
      exact Finset.sum_eq_zero (fun k _ => by rw [hall k, mul_zero])
    obtain ⟨k, hk⟩ := hDk
    have hfeq : f = N k / D k := by rw [← hDN k, mul_div_cancel_right₀ _ hk]
    rw [hfeq]
    exact div_mem (Subfield.sum_mem _ fun i _ => mul_mem (hRconst _) (hGR i))
      (Subfield.sum_mem _ fun j _ => mul_mem (hRconst _) (hHR j))

  have hTR : ∀ y : ↥(fieldBar q M'), y ∈ T → y ∈ R := by
    let R' : IntermediateField ↥k₀ ↥(fieldBar q M') :=
      R.toIntermediateField (fun x => hRconst ⟨algebraMap ↥k₀ Ω x, K₁.algebraMap_mem x⟩)
    have hle : T ≤ R' := by
      refine sup_le (IntermediateField.adjoin_le_iff.2 ?_) ?_
      · rintro _ ⟨c, hc, rfl⟩
        exact hRconst ⟨c, hc⟩
      · intro f hf
        exact hF₀R f hf
    intro y hy
    exact hle hy
  have hsurj : Function.Surjective ψ := by
    intro t
    obtain ⟨x, hx⟩ := hTR t.1 t.2
    exact ⟨x, Subtype.ext hx⟩
  refine ⟨RingEquiv.ofBijective ψ ⟨hinj, hsurj⟩, fun f => ?_⟩
  exact hψ f

end S_ModularCurve_FullLevel_exists_ringEquiv_laurentBaseChange_levelField_coe_eq_coeffMap
end P2MW
export P2MW.S_ModularCurve_FullLevel_exists_ringEquiv_laurentBaseChange_levelField_coe_eq_coeffMap (solution)
