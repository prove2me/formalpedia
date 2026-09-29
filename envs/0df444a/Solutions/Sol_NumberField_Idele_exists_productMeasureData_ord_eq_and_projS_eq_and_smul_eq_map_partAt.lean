-- Prove2me | solution 1 for NumberField.Idele.exists_productMeasureData_ord_eq_and_projS_eq_and_smul_eq_map_partAt
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/d7c1a75d-d0b8-5728-8d5d-f18dabcaeea8

import Definitions.Def_NumberField_IdeleProductMeasure
import Definitions.Def_UnramifiedWhittaker_ZetaIntegrand
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_Idele_exists_productMeasureData_ord_eq_and_projS_eq_and_smul_eq_map_partAt

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain NumberField.AdelicLevel NumberField.AdeleRing

namespace PZExistsSol

open NumberField.Idele

variable (F : Type) [Field F] [NumberField F]

noncomputable def ordHom (v : HeightOneSpectrum (𝓞 F)) : (AdeleRing (𝓞 F) F)ˣ →* Multiplicative ℤ where
  toFun a := Multiplicative.ofAdd (ord F v a)
  map_one' := by rw [ord_one]; rfl
  map_mul' a b := by rw [ord_mul]; rfl

theorem ord_zpow (v : HeightOneSpectrum (𝓞 F)) (a : (AdeleRing (𝓞 F) F)ˣ) (n : ℤ) :
    ord F v (a ^ n) = n * ord F v a := by
  have h : Multiplicative.ofAdd (ord F v (a ^ n)) = Multiplicative.ofAdd (ord F v a) ^ n :=
    map_zpow (ordHom F v) a n
  rw [← ofAdd_zsmul] at h
  rw [Multiplicative.ofAdd.injective h, smul_eq_mul]

open scoped Classical in

theorem partAt_uniformizerIdele_of_not_mem (S : Finset (HeightOneSpectrum (𝓞 F)))
    {v : HeightOneSpectrum (𝓞 F)} (hv : v ∉ S) : partAt F S (AutomorphicForm.uniformizerIdele F v) = 1 := by
  refine Units.ext (Prod.ext rfl (Subtype.ext (funext fun w => ?_)))
  show (if w ∈ S then ((localUnit (𝓞 F) F v (uniformizerUnit F v) : (FiniteAdeleRing (𝓞 F) F)ˣ) :
      FiniteAdeleRing (𝓞 F) F) w else 1) = (1 : FiniteAdeleRing (𝓞 F) F) w
  by_cases hw : w ∈ S
  · rw [if_pos hw]
    have hwv : w ≠ v := fun h => hv (h ▸ hw)
    rw [localUnit_apply_of_ne (𝓞 F) F v (uniformizerUnit F v) hwv]
    rfl
  · rw [if_neg hw]
    rfl

theorem mem_unitIdelesOutside_iff_ord (T : Set (HeightOneSpectrum (𝓞 F))) (a : (AdeleRing (𝓞 F) F)ˣ) :
    a ∈ NumberField.AdeleRing.unitIdelesOutside (𝓞 F) F T ↔ ∀ w, w ∉ T → ord F w a = 0 := by
  rw [NumberField.AdeleRing.mem_unitIdelesOutside_iff, IsDedekindDomain.FiniteAdeleRing.mem_unitIdelesOutside_iff]
  refine forall_congr' fun w => imp_congr_right fun _ => ?_
  rw [ord_eq_zero_iff]
  rfl

theorem mem_image_uniformizerIdele_zpow_mul_iff (T' : Set (HeightOneSpectrum (𝓞 F)))
    {v : HeightOneSpectrum (𝓞 F)} (hv : v ∉ T') (n : ℤ) (a : (AdeleRing (𝓞 F) F)ˣ) :
    a ∈ (fun b : (AdeleRing (𝓞 F) F)ˣ => AutomorphicForm.uniformizerIdele F v ^ n * b) ''
        (NumberField.AdeleRing.unitIdelesOutside (𝓞 F) F T' : Set (AdeleRing (𝓞 F) F)ˣ) ↔
      a ∈ (NumberField.AdeleRing.unitIdelesOutside (𝓞 F) F (insert v T') : Set (AdeleRing (𝓞 F) F)ˣ) ∧
        ord F v a = n := by
  constructor
  · rintro ⟨b, hb, rfl⟩
    rw [SetLike.mem_coe, mem_unitIdelesOutside_iff_ord] at hb
    refine ⟨?_, ?_⟩
    · rw [SetLike.mem_coe, mem_unitIdelesOutside_iff_ord]
      intro w hw
      rw [Set.mem_insert_iff, not_or] at hw
      rw [ord_mul, ord_zpow, ord_uniformizerIdele_of_ne F hw.1, mul_zero, zero_add, hb w hw.2]
    · rw [ord_mul, ord_zpow, ord_uniformizerIdele_self, mul_one, hb v hv, add_zero]
  · rintro ⟨ha, hn⟩
    rw [SetLike.mem_coe, mem_unitIdelesOutside_iff_ord] at ha
    refine ⟨AutomorphicForm.uniformizerIdele F v ^ (-n) * a, ?_, ?_⟩
    · rw [SetLike.mem_coe, mem_unitIdelesOutside_iff_ord]
      intro w hw
      by_cases hwv : w = v
      · rw [hwv, ord_mul, ord_zpow, ord_uniformizerIdele_self, mul_one, hn, neg_add_cancel]
      · rw [ord_mul, ord_zpow, ord_uniformizerIdele_of_ne F hwv, mul_zero, zero_add]
        exact ha w fun h => (Set.mem_insert_iff.mp h).elim hwv hw
    · show AutomorphicForm.uniformizerIdele F v ^ n * (AutomorphicForm.uniformizerIdele F v ^ (-n) * a) = a
      rw [← mul_assoc, ← zpow_add, add_neg_cancel, zpow_zero, one_mul]

theorem iUnion_image_uniformizerIdele_zpow_mul (T' : Set (HeightOneSpectrum (𝓞 F)))
    {v : HeightOneSpectrum (𝓞 F)} (hv : v ∉ T') :
    (⋃ n : ℤ, (fun b : (AdeleRing (𝓞 F) F)ˣ => AutomorphicForm.uniformizerIdele F v ^ n * b) ''
        (NumberField.AdeleRing.unitIdelesOutside (𝓞 F) F T' : Set (AdeleRing (𝓞 F) F)ˣ)) =
      (NumberField.AdeleRing.unitIdelesOutside (𝓞 F) F (insert v T') : Set (AdeleRing (𝓞 F) F)ˣ) := by
  ext a
  rw [Set.mem_iUnion]
  constructor
  · rintro ⟨n, h⟩
    exact ((mem_image_uniformizerIdele_zpow_mul_iff F T' hv n a).mp h).1
  · intro h
    exact ⟨ord F v a, (mem_image_uniformizerIdele_zpow_mul_iff F T' hv _ a).mpr ⟨h, rfl⟩⟩

theorem pairwise_disjoint_image_uniformizerIdele_zpow_mul (T' : Set (HeightOneSpectrum (𝓞 F)))
    {v : HeightOneSpectrum (𝓞 F)} (hv : v ∉ T') :
    Pairwise (Function.onFun Disjoint fun n : ℤ =>
      (fun b : (AdeleRing (𝓞 F) F)ˣ => AutomorphicForm.uniformizerIdele F v ^ n * b) ''
        (NumberField.AdeleRing.unitIdelesOutside (𝓞 F) F T' : Set (AdeleRing (𝓞 F) F)ˣ)) := by
  intro m n hmn
  refine Set.disjoint_left.mpr fun a ham han => hmn ?_
  exact ((mem_image_uniformizerIdele_zpow_mul_iff F T' hv m a).mp ham).2.symm.trans
    ((mem_image_uniformizerIdele_zpow_mul_iff F T' hv n a).mp han).2

theorem integrableOn_and_integral_eq
    [MeasurableSpace (AdeleRing (𝓞 F) F)ˣ] [BorelSpace (AdeleRing (𝓞 F) F)ˣ]
    (ν : Measure (AdeleRing (𝓞 F) F)ˣ) [ν.IsHaarMeasure]
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    (f : (AdeleRing (𝓞 F) F)ˣ → ℂ) (φ : HeightOneSpectrum (𝓞 F) → ℤ → ℂ)
    (hf : Integrable f (Measure.map (partAt F S)
      (ν.restrict (NumberField.AdeleRing.unitIdelesOutside (𝓞 F) F (↑S) : Set (AdeleRing (𝓞 F) F)ˣ)))) :
    ∀ (L : List (HeightOneSpectrum (𝓞 F))), (∀ v ∈ L, v ∉ S) → L.Nodup →
      (∀ v ∈ L, Summable fun m : ℤ => ‖φ v m‖) →
        IntegrableOn (fun a => f (partAt F S a) * (L.map fun v => φ v (ord F v a)).prod)
            (NumberField.AdeleRing.unitIdelesOutside (𝓞 F) F (↑S ∪ {v | v ∈ L}) : Set (AdeleRing (𝓞 F) F)ˣ) ν ∧
          (∫ a in (NumberField.AdeleRing.unitIdelesOutside (𝓞 F) F (↑S ∪ {v | v ∈ L}) : Set (AdeleRing (𝓞 F) F)ˣ),
              f (partAt F S a) * (L.map fun v => φ v (ord F v a)).prod ∂ν) =
            (∫ a, f a ∂(Measure.map (partAt F S)
              (ν.restrict (NumberField.AdeleRing.unitIdelesOutside (𝓞 F) F (↑S) : Set (AdeleRing (𝓞 F) F)ˣ)))) *
              (L.map fun v => ∑' m : ℤ, φ v m).prod := by
  intro L
  induction L with
  | nil =>
    intro _ _ _
    have hT : (↑S ∪ {v | v ∈ ([] : List (HeightOneSpectrum (𝓞 F)))} : Set (HeightOneSpectrum (𝓞 F))) = ↑S := by
      ext w
      simp only [Set.mem_union, Set.mem_setOf_eq, List.not_mem_nil, or_false]
    simp only [List.map_nil, List.prod_nil, mul_one, hT]
    have hφm : AEMeasurable (partAt F S) (ν.restrict
        (NumberField.AdeleRing.unitIdelesOutside (𝓞 F) F (↑S) : Set (AdeleRing (𝓞 F) F)ˣ)) :=
      (continuous_partAt F S).measurable.aemeasurable
    exact ⟨(integrable_map_measure hf.aestronglyMeasurable hφm).mp hf,
      (integral_map hφm hf.aestronglyMeasurable).symm⟩
  | cons v L' IH =>
    intro hLS hL hφ
    have hvS : v ∉ S := hLS v List.mem_cons_self
    have hLS' : ∀ w ∈ L', w ∉ S := fun w hw => hLS w (List.mem_cons_of_mem v hw)
    have hvL' : v ∉ L' := (List.nodup_cons.mp hL).1
    have hL' : L'.Nodup := (List.nodup_cons.mp hL).2
    have hφv : Summable fun m : ℤ => ‖φ v m‖ := hφ v List.mem_cons_self
    have hφ' : ∀ w ∈ L', Summable fun m : ℤ => ‖φ w m‖ := fun w hw => hφ w (List.mem_cons_of_mem v hw)
    obtain ⟨IHi, IHe⟩ := IH hLS' hL' hφ'

    have hv' : v ∉ (↑S ∪ {w | w ∈ L'} : Set (HeightOneSpectrum (𝓞 F))) := by
      rintro (h | h)
      · exact hvS (Finset.mem_coe.mp h)
      · exact hvL' h
    have hT : (↑S ∪ {w | w ∈ v :: L'} : Set (HeightOneSpectrum (𝓞 F))) = insert v (↑S ∪ {w | w ∈ L'}) := by
      ext w
      simp only [Set.mem_union, Set.mem_setOf_eq, List.mem_cons, Set.mem_insert_iff, Finset.mem_coe]
      tauto
    rw [hT, ← iUnion_image_uniformizerIdele_zpow_mul F _ hv']

    have hkey : ∀ (n : ℤ) (b : (AdeleRing (𝓞 F) F)ˣ),
        b ∈ (NumberField.AdeleRing.unitIdelesOutside (𝓞 F) F (↑S ∪ {w | w ∈ L'}) : Set (AdeleRing (𝓞 F) F)ˣ) →
        f (partAt F S (AutomorphicForm.uniformizerIdele F v ^ n * b)) *
            ((v :: L').map fun w => φ w (ord F w (AutomorphicForm.uniformizerIdele F v ^ n * b))).prod =
          φ v n * (f (partAt F S b) * (L'.map fun w => φ w (ord F w b)).prod) := by
      intro n b hb
      rw [SetLike.mem_coe, mem_unitIdelesOutside_iff_ord] at hb
      have h1 : partAt F S (AutomorphicForm.uniformizerIdele F v ^ n * b) = partAt F S b := by
        rw [map_mul, map_zpow, partAt_uniformizerIdele_of_not_mem F S hvS, one_zpow, one_mul]
      have h2 : ord F v (AutomorphicForm.uniformizerIdele F v ^ n * b) = n := by
        rw [ord_mul, ord_zpow, ord_uniformizerIdele_self, mul_one, hb v hv', add_zero]
      have h3 : ((L'.map fun w => φ w (ord F w (AutomorphicForm.uniformizerIdele F v ^ n * b))) :
          List ℂ) = L'.map fun w => φ w (ord F w b) := by
        refine List.map_congr_left fun w hw => ?_
        have hwv : w ≠ v := fun h => hvL' (h ▸ hw)
        rw [ord_mul, ord_zpow, ord_uniformizerIdele_of_ne F hwv, mul_zero, zero_add]
      rw [List.map_cons, List.prod_cons, h1, h2, h3]
      ring

    have hmp : ∀ n : ℤ, MeasurePreserving
        (fun b : (AdeleRing (𝓞 F) F)ˣ => AutomorphicForm.uniformizerIdele F v ^ n * b) ν ν :=
      fun n => measurePreserving_mul_left ν _
    have hme : ∀ n : ℤ, MeasurableEmbedding
        fun b : (AdeleRing (𝓞 F) F)ˣ => AutomorphicForm.uniformizerIdele F v ^ n * b :=
      fun n => (MeasurableEquiv.mulLeft (AutomorphicForm.uniformizerIdele F v ^ n)).measurableEmbedding
    have hU' : MeasurableSet
        (NumberField.AdeleRing.unitIdelesOutside (𝓞 F) F (↑S ∪ {w | w ∈ L'}) : Set (AdeleRing (𝓞 F) F)ˣ) :=
      (isOpen_unitIdelesOutside F _).measurableSet
    have hmeas : ∀ n : ℤ, MeasurableSet
        ((fun b : (AdeleRing (𝓞 F) F)ˣ => AutomorphicForm.uniformizerIdele F v ^ n * b) ''
          (NumberField.AdeleRing.unitIdelesOutside (𝓞 F) F (↑S ∪ {w | w ∈ L'}) : Set (AdeleRing (𝓞 F) F)ˣ)) :=
      fun n => (hme n).measurableSet_image.mpr hU'

    have hpi : ∀ n : ℤ, IntegrableOn (fun a => f (partAt F S a) * ((v :: L').map fun w => φ w (ord F w a)).prod)
        ((fun b : (AdeleRing (𝓞 F) F)ˣ => AutomorphicForm.uniformizerIdele F v ^ n * b) ''
          (NumberField.AdeleRing.unitIdelesOutside (𝓞 F) F (↑S ∪ {w | w ∈ L'}) : Set (AdeleRing (𝓞 F) F)ˣ))
        ν := by
      intro n
      have hc0 : IntegrableOn (fun b => φ v n * (f (partAt F S b) * (L'.map fun w => φ w (ord F w b)).prod))
          (NumberField.AdeleRing.unitIdelesOutside (𝓞 F) F (↑S ∪ {w | w ∈ L'}) : Set (AdeleRing (𝓞 F) F)ˣ)
          ν :=
        Integrable.const_mul IHi (φ v n)
      have hc : IntegrableOn (fun b => f (partAt F S (AutomorphicForm.uniformizerIdele F v ^ n * b)) *
            ((v :: L').map fun w => φ w (ord F w (AutomorphicForm.uniformizerIdele F v ^ n * b))).prod)
          (NumberField.AdeleRing.unitIdelesOutside (𝓞 F) F (↑S ∪ {w | w ∈ L'}) : Set (AdeleRing (𝓞 F) F)ˣ)
          ν :=
        hc0.congr_fun (fun b hb => (hkey n b hb).symm) hU'
      exact (((hmp n).restrict_image_emb (hme n) _).integrable_comp_emb (hme n)
        (g := fun a => f (partAt F S a) * ((v :: L').map fun w => φ w (ord F w a)).prod)).mp hc
    have hnorm : ∀ n : ℤ, (∫ a in (fun b : (AdeleRing (𝓞 F) F)ˣ => AutomorphicForm.uniformizerIdele F v ^ n * b) ''
          (NumberField.AdeleRing.unitIdelesOutside (𝓞 F) F (↑S ∪ {w | w ∈ L'}) : Set (AdeleRing (𝓞 F) F)ˣ),
          ‖f (partAt F S a) * ((v :: L').map fun w => φ w (ord F w a)).prod‖ ∂ν) =
        ‖φ v n‖ * ∫ b in (NumberField.AdeleRing.unitIdelesOutside (𝓞 F) F (↑S ∪ {w | w ∈ L'}) :
            Set (AdeleRing (𝓞 F) F)ˣ),
          ‖f (partAt F S b) * (L'.map fun w => φ w (ord F w b)).prod‖ ∂ν := by
      intro n
      rw [(hmp n).setIntegral_image_emb (hme n), ← integral_const_mul]
      refine setIntegral_congr_fun hU' fun b hb => ?_
      show ‖f (partAt F S (AutomorphicForm.uniformizerIdele F v ^ n * b)) *
          ((v :: L').map fun w => φ w (ord F w (AutomorphicForm.uniformizerIdele F v ^ n * b))).prod‖ =
        ‖φ v n‖ * ‖f (partAt F S b) * (L'.map fun w => φ w (ord F w b)).prod‖
      rw [hkey n b hb, norm_mul]
    have hsum : Summable fun n : ℤ => ∫ a in (fun b : (AdeleRing (𝓞 F) F)ˣ =>
          AutomorphicForm.uniformizerIdele F v ^ n * b) ''
          (NumberField.AdeleRing.unitIdelesOutside (𝓞 F) F (↑S ∪ {w | w ∈ L'}) : Set (AdeleRing (𝓞 F) F)ˣ),
          ‖f (partAt F S a) * ((v :: L').map fun w => φ w (ord F w a)).prod‖ ∂ν := by
      simp_rw [hnorm]
      exact hφv.mul_right _
    have hint := integrableOn_iUnion_of_summable_integral_norm hpi hsum
    refine ⟨hint, ?_⟩

    rw [integral_iUnion hmeas (pairwise_disjoint_image_uniformizerIdele_zpow_mul F _ hv') hint]
    have hval : ∀ n : ℤ, (∫ a in (fun b : (AdeleRing (𝓞 F) F)ˣ => AutomorphicForm.uniformizerIdele F v ^ n * b) ''
          (NumberField.AdeleRing.unitIdelesOutside (𝓞 F) F (↑S ∪ {w | w ∈ L'}) : Set (AdeleRing (𝓞 F) F)ˣ),
          f (partAt F S a) * ((v :: L').map fun w => φ w (ord F w a)).prod ∂ν) =
        φ v n * ((∫ a, f a ∂(Measure.map (partAt F S)
              (ν.restrict (NumberField.AdeleRing.unitIdelesOutside (𝓞 F) F (↑S) : Set (AdeleRing (𝓞 F) F)ˣ)))) *
            (L'.map fun w => ∑' m : ℤ, φ w m).prod) := by
      intro n
      rw [(hmp n).setIntegral_image_emb (hme n), ← IHe, ← integral_const_mul]
      exact setIntegral_congr_fun hU' fun b hb => hkey n b hb
    simp_rw [hval]
    rw [tsum_mul_right, List.map_cons, List.prod_cons]
    ring

noncomputable def productMeasureDataOf
    [MeasurableSpace (AdeleRing (𝓞 F) F)ˣ] [BorelSpace (AdeleRing (𝓞 F) F)ˣ]
    (S : Finset (HeightOneSpectrum (𝓞 F))) (ν : Measure (AdeleRing (𝓞 F) F)ˣ) [ν.IsHaarMeasure] :
    UnramifiedWhittaker.ProductMeasureData S ν where
  c := 1
  c_pos := one_pos
  νS := Measure.map (partAt F S)
    (ν.restrict (NumberField.AdeleRing.unitIdelesOutside (𝓞 F) F (↑S) : Set (AdeleRing (𝓞 F) F)ˣ))
  projS := partAt F S
  ord := ord F
  projS_off a _ hv := partAt_snd_of_not_mem F S a hv
  decomp L hLS hL a ha := ⟨unitPart F S a, unitPart_fst F S a, unitPart_snd_of_mem F S a,
    finitePartUnits_unitPart_mem_unitIdeles F S a, eq_partAt_mul_prod_mul_unitPart F S L hLS hL a ha⟩
  tonelli L hLS hL f φ hf hφ := by
    obtain ⟨h1, h2⟩ := integrableOn_and_integral_eq F ν S f φ hf L hLS hL hφ
    exact ⟨h1, by rw [h2, Complex.ofReal_one, one_mul]⟩
  measurableSet L _ _ := (isOpen_unitIdelesOutside F _).measurableSet

end PZExistsSol

theorem solution
    (K : Type) [Field K] [NumberField K]
    [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ] [BorelSpace (AdeleRing (𝓞 K) K)ˣ]
    (SK : Finset (HeightOneSpectrum (𝓞 K)))
    (νZK : Measure (AdeleRing (𝓞 K) K)ˣ) [νZK.IsHaarMeasure] :
    ∃ PZ : UnramifiedWhittaker.ProductMeasureData SK νZK,
      PZ.ord = NumberField.Idele.ord K ∧
      PZ.projS = NumberField.Idele.partAt K SK ∧
      ENNReal.ofReal PZ.c • PZ.νS = Measure.map (NumberField.Idele.partAt K SK)
        (νZK.restrict (NumberField.AdeleRing.unitIdelesOutside (𝓞 K) K ↑SK)) := by
  refine ⟨PZExistsSol.productMeasureDataOf K SK νZK, rfl, rfl, ?_⟩
  show ENNReal.ofReal 1 • Measure.map (NumberField.Idele.partAt K SK)
      (νZK.restrict (NumberField.AdeleRing.unitIdelesOutside (𝓞 K) K ↑SK)) = _
  rw [ENNReal.ofReal_one, one_smul]

end S_NumberField_Idele_exists_productMeasureData_ord_eq_and_projS_eq_and_smul_eq_map_partAt
end P2MW
export P2MW.S_NumberField_Idele_exists_productMeasureData_ord_eq_and_projS_eq_and_smul_eq_map_partAt (solution)
