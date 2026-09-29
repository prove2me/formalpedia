-- Prove2me | solution 1 for LanglandsTunnell.RankinSelberg.exists_pos_forall_rsFinIntegral_eq_mul_of_support_subset_unipotent_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/71dedcca-61d9-5cfa-ab93-c630a63387b3

import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_NumberField_TateGlobalZeta
import Theorems.Thm_HaarQuotient_lintegral_eq_lintegral_lintegral_mul_out
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_RankinSelberg_exists_pos_forall_rsFinIntegral_eq_mul_of_support_subset_unipotent_mul

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory AutomorphicForm
open NumberField.TateGlobal
open scoped ENNReal Pointwise

namespace Ws23Support

section Generic

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]

omit [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G] in
theorem mul_mem_coe_mul_coe_iff (H U : Subgroup G) {h : G} (hh : h ∈ H) (g : G) :
    h * g ∈ (H : Set G) * (U : Set G) ↔ g ∈ (H : Set G) * (U : Set G) := by
  constructor
  · intro hg
    obtain ⟨a, ha, b, hb, hab⟩ := Set.mem_mul.1 hg
    refine Set.mem_mul.2 ⟨h⁻¹ * a, H.mul_mem (H.inv_mem hh) ha, b, hb, ?_⟩
    rw [mul_assoc, hab, inv_mul_cancel_left]
  · intro hg
    obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_mul.1 hg
    exact Set.mem_mul.2 ⟨h * a, H.mul_mem hh ha, b, hb, by rw [mul_assoc]⟩

theorem measure_eq_measure_inter_mul_withDensity_mul (μ : Measure G) [μ.IsHaarMeasure]
    (H : Subgroup G) (hH : IsClosed (H : Set G))
    (μH : Measure H) [μH.IsHaarMeasure] [μH.IsMulRightInvariant]
    (U : Subgroup G) (hUo : IsOpen (U : Set G)) :
    μ U = μH {x : H | (x : G) ∈ U} *
      (μ.withDensity (HaarQuotient.density H μH)) ((H : Set G) * (U : Set G)) := by
  classical
  set E : Set G := (H : Set G) * (U : Set G) with hE
  set U' : Set H := {x : H | (x : G) ∈ U} with hU'
  have hEo : IsOpen E := hUo.mul_left

  have hI : ∀ g : G, μH {x : H | (x : G) * g ∈ (U : Set G)} = E.indicator (fun _ => μH U') g := by
    intro g
    by_cases hg : g ∈ E
    · rw [Set.indicator_of_mem hg]
      obtain ⟨h, hh, u, hu, rfl⟩ := hg
      have hset : {x : H | (x : G) * (h * u) ∈ (U : Set G)} = (fun x : H => x * ⟨h, hh⟩) ⁻¹' U' := by
        ext x
        simp only [Set.mem_setOf_eq, Set.mem_preimage, hU', Subgroup.coe_mul, SetLike.mem_coe]
        rw [← mul_assoc]
        exact ⟨fun hx => by simpa using U.mul_mem hx (U.inv_mem hu), fun hx => U.mul_mem hx hu⟩
      rw [hset, measure_preimage_mul_right]
    · rw [Set.indicator_of_notMem hg]
      have hset : {x : H | (x : G) * g ∈ (U : Set G)} = ∅ := by
        ext x
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
        intro hx
        exact hg ⟨(x : G)⁻¹, H.inv_mem x.2, (x : G) * g, hx, inv_mul_cancel_left _ _⟩
      rw [hset, measure_empty]

  have hq := HaarQuotient.lintegral_eq_lintegral_lintegral_mul_out μ H hH μH
    ((U : Set G).indicator 1) (measurable_one.indicator hUo.measurableSet)
  rw [lintegral_indicator_one hUo.measurableSet] at hq
  have hinner : ∀ q : MulAction.orbitRel.Quotient H G,
      (∫⁻ x : H, (U : Set G).indicator (1 : G → ℝ≥0∞) ((x : G) * q.out) ∂μH) =
        E.indicator (fun _ => μH U') q.out := by
    intro q
    rw [← hI]
    have hfun : (fun x : H => (U : Set G).indicator (1 : G → ℝ≥0∞) ((x : G) * q.out)) =
        {x : H | (x : G) * q.out ∈ (U : Set G)}.indicator 1 := by
      funext x
      simp only [Set.indicator, Set.mem_setOf_eq, Pi.one_apply]
    rw [hfun, lintegral_indicator_one]
    exact (hUo.preimage (by fun_prop : Continuous fun x : H => (x : G) * q.out)).measurableSet
  simp_rw [hinner] at hq

  set Ebar : Set (MulAction.orbitRel.Quotient H G) := Quotient.out ⁻¹' E with hEbar
  have hpre : (Quotient.mk'' : G → MulAction.orbitRel.Quotient H G) ⁻¹' Ebar = E := by
    ext g
    simp only [Set.mem_preimage, hEbar]
    have hmem : (Quotient.mk'' g : MulAction.orbitRel.Quotient H G).out ∈ MulAction.orbit H g :=
      MulAction.orbitRel_apply.1 (Quotient.mk_out g)
    obtain ⟨h, hh⟩ := MulAction.mem_orbit_iff.1 hmem
    rw [← hh, Subgroup.smul_def, smul_eq_mul]
    exact mul_mem_coe_mul_coe_iff H U h.2 g
  have hEbar_meas : MeasurableSet Ebar := by
    rw [measurableSet_quotient, hpre]
    exact hEo.measurableSet
  have hind : (fun q : MulAction.orbitRel.Quotient H G => E.indicator (fun _ => μH U') q.out) =
      Ebar.indicator fun _ => μH U' := by
    funext q
    simp only [Set.indicator, hEbar, Set.mem_preimage]
  rw [hind, lintegral_indicator_const hEbar_meas] at hq
  rw [hq]
  congr 1
  unfold HaarQuotient.measure
  rw [Measure.map_apply measurable_quotient_mk'' hEbar_meas, hpre]

theorem withDensity_mul_pos_and_lt_top (μ : Measure G) [μ.IsHaarMeasure]
    (H : Subgroup G) (hH : IsClosed (H : Set G))
    (μH : Measure H) [μH.IsHaarMeasure] [μH.IsMulRightInvariant]
    (U : Subgroup G) (hUc : IsCompact (U : Set G)) (hUo : IsOpen (U : Set G)) :
    0 < (μ.withDensity (HaarQuotient.density H μH)) ((H : Set G) * (U : Set G)) ∧
      (μ.withDensity (HaarQuotient.density H μH)) ((H : Set G) * (U : Set G)) < ∞ := by
  have h := measure_eq_measure_inter_mul_withDensity_mul μ H hH μH U hUo
  set U' : Set H := {x : H | (x : G) ∈ U} with hU'
  have hU'o : IsOpen U' := hUo.preimage continuous_subtype_val
  have hU'c : IsCompact U' := hH.isClosedEmbedding_subtypeVal.isCompact_preimage hUc
  have hm₀pos : 0 < μH U' := hU'o.measure_pos μH ⟨1, U.one_mem⟩
  have hm₀top : μH U' < ∞ := hU'c.measure_lt_top
  have hUpos : 0 < μ U := hUo.measure_pos μ ⟨1, U.one_mem⟩
  have hUtop : μ (U : Set G) < ∞ := hUc.measure_lt_top
  constructor
  · rw [pos_iff_ne_zero]
    intro h0
    rw [h0, mul_zero] at h
    exact hUpos.ne' h
  · rw [lt_top_iff_ne_top]
    intro ht
    rw [ht, ENNReal.mul_top hm₀pos.ne'] at h
    exact hUtop.ne h

end Generic

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

abbrev Gf : Type := ↥(finiteAdelicGL2Subgroup ℚ)

theorem coe_adelicUnipotent_eq :
    ((adelicUnipotent ℚ : Subgroup (AdelicGL2 (𝓞 ℚ) ℚ)) : Set (AdelicGL2 (𝓞 ℚ) ℚ)) =
      {g : AdelicGL2 (𝓞 ℚ) ℚ | ((g : AdelicGL2 (𝓞 ℚ) ℚ) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) 0 0 = 1 ∧
        ((g : AdelicGL2 (𝓞 ℚ) ℚ) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) 1 0 = 0 ∧
        ((g : AdelicGL2 (𝓞 ℚ) ℚ) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) 1 1 = 1} := by
  ext g
  simp only [SetLike.mem_coe, MonoidHom.mem_range, Set.mem_setOf_eq]
  constructor
  · rintro ⟨x, rfl⟩
    have h : ((unipotentGL2Hom x : AdelicGL2 (𝓞 ℚ) ℚ) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) =
        !![1, x.toAdd; 0, 1] := rfl
    simp [h]
  · rintro ⟨h00, h10, h11⟩
    refine ⟨Multiplicative.ofAdd ((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) 0 1), ?_⟩
    refine Units.ext ?_
    change ((unipotentGL2 ((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) 0 1) : AdelicGL2 (𝓞 ℚ) ℚ) :
      Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) = g
    rw [unipotentGL2_coe]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h00, h10, h11]

theorem isClosed_adelicUnipotent :
    IsClosed ((adelicUnipotent ℚ : Subgroup (AdelicGL2 (𝓞 ℚ) ℚ)) : Set (AdelicGL2 (𝓞 ℚ) ℚ)) := by
  rw [coe_adelicUnipotent_eq]
  have hc : ∀ i j : Fin 2, Continuous fun g : AdelicGL2 (𝓞 ℚ) ℚ =>
      (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) i j :=
    fun i j => Units.continuous_val.matrix_elem i j
  exact ((isClosed_singleton.preimage (hc 0 0)).inter
    ((isClosed_singleton.preimage (hc 1 0)).inter (isClosed_singleton.preimage (hc 1 1))))

theorem isClosed_finUnipotent : IsClosed ((RSCarrier.finUnipotent : Subgroup Gf) : Set Gf) :=
  isClosed_adelicUnipotent.preimage continuous_subtype_val

theorem finUnipotent_mul_comm (a b : RSCarrier.finUnipotent) : a * b = b * a := by
  obtain ⟨x, hx⟩ := Subgroup.mem_subgroupOf.1 a.2
  obtain ⟨y, hy⟩ := Subgroup.mem_subgroupOf.1 b.2
  refine Subtype.ext (Subtype.ext ?_)
  change ((a : Gf) : AdelicGL2 (𝓞 ℚ) ℚ) * ((b : Gf) : AdelicGL2 (𝓞 ℚ) ℚ) =
    ((b : Gf) : AdelicGL2 (𝓞 ℚ) ℚ) * ((a : Gf) : AdelicGL2 (𝓞 ℚ) ℚ)
  rw [← hx, ← hy, ← map_mul, ← map_mul, mul_comm]

theorem isMulRightInvariant_finUnipotent (μN : Measure RSCarrier.finUnipotent) [μN.IsMulLeftInvariant] :
    μN.IsMulRightInvariant := by
  refine ⟨fun n => ?_⟩
  have h : (fun x : RSCarrier.finUnipotent => x * n) = fun x => n * x := funext fun x => finUnipotent_mul_comm x n
  rw [h]
  exact map_mul_left_eq_self μN n

theorem det_of_mem_finUnipotent {n : Gf} (hn : n ∈ RSCarrier.finUnipotent) :
    Matrix.GeneralLinearGroup.det ((n : AdelicGL2 (𝓞 ℚ) ℚ)) = 1 := by
  obtain ⟨x, hx⟩ := Subgroup.mem_subgroupOf.1 hn
  rw [← hx]
  refine Units.ext ?_
  change Matrix.det ((unipotentGL2 x.toAdd : AdelicGL2 (𝓞 ℚ) ℚ) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) = 1
  rw [unipotentGL2_coe, Matrix.det_fin_two_of]
  ring

theorem main [SecondCountableTopology (AdelicGL2 (𝓞 ℚ) ℚ)]
    (μ : Measure (finiteAdelicGL2Subgroup ℚ)) [μ.IsHaarMeasure]
    (μN : Measure RSCarrier.finUnipotent) [μN.IsHaarMeasure]
    (U : Subgroup (finiteAdelicGL2Subgroup ℚ))
    (hUc : IsCompact (U : Set (finiteAdelicGL2Subgroup ℚ)))
    (hUo : IsOpen (U : Set (finiteAdelicGL2Subgroup ℚ)))
    (hUdet : ∀ u ∈ U, ideleNorm ℚ (Matrix.GeneralLinearGroup.det ((u : finiteAdelicGL2Subgroup ℚ) : AdelicGL2 (𝓞 ℚ) ℚ)) = 1) :
    ∃ c : ℝ, 0 < c ∧
      ∀ (s : ℂ) (W F : finiteAdelicGL2Subgroup ℚ → ℂ),
        (∀ (n : RSCarrier.finUnipotent) (g : finiteAdelicGL2Subgroup ℚ),
          W ((n : finiteAdelicGL2Subgroup ℚ) * g) * F ((n : finiteAdelicGL2Subgroup ℚ) * g) = W g * F g) →
        (∀ g : finiteAdelicGL2Subgroup ℚ, W g * F g ≠ 0 →
          ∃ (n : RSCarrier.finUnipotent) (u : finiteAdelicGL2Subgroup ℚ), u ∈ U ∧
            g = (n : finiteAdelicGL2Subgroup ℚ) * u) →
        (∀ u ∈ U, W u * F u = W 1 * F 1) →
        RSCarrier.rsFinIntegral μ μN s W F = (c : ℂ) * (W 1 * F 1) := by
  haveI : LocallyCompactSpace Gf :=
    (isClosed_finiteAdelicGL2Subgroup ℚ).isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology Gf := Topology.IsInducing.subtypeVal.secondCountableTopology
  haveI : μN.IsMulRightInvariant := isMulRightInvariant_finUnipotent μN
  set ν : Measure Gf := μ.withDensity (HaarQuotient.density (RSCarrier.finUnipotent : Subgroup Gf) μN) with hν
  set E : Set Gf := ((RSCarrier.finUnipotent : Subgroup Gf) : Set Gf) * (U : Set Gf) with hE
  have hEo : IsOpen E := hUo.mul_left
  obtain ⟨hpos, htop⟩ :=
    withDensity_mul_pos_and_lt_top μ (RSCarrier.finUnipotent : Subgroup Gf) isClosed_finUnipotent μN U hUc hUo
  refine ⟨(ν E).toReal, ENNReal.toReal_pos hpos.ne' htop.ne, fun s W F hinv hsupp hconst => ?_⟩

  have hpt : ∀ g : Gf,
      W g * F g * ((ideleNorm ℚ (Matrix.GeneralLinearGroup.det ((g : Gf) : AdelicGL2 (𝓞 ℚ) ℚ)) : ℝ) : ℂ) ^
          (s - 1 / 2) =
        E.indicator (fun _ => W 1 * F 1) g := by
    intro g
    by_cases hg : g ∈ E
    · rw [Set.indicator_of_mem hg]
      obtain ⟨n, hn, u, hu, rfl⟩ := hg
      have hP : W (n * u) * F (n * u) = W 1 * F 1 := by
        rw [← hconst u hu]
        exact hinv ⟨n, hn⟩ u
      have h1 : ideleNorm ℚ (1 : (AdeleRing (𝓞 ℚ) ℚ)ˣ) = 1 := by
        have hp : 0 < ideleNorm ℚ (1 : (AdeleRing (𝓞 ℚ) ℚ)ˣ) := ideleNorm_pos _
        have hm : ideleNorm ℚ ((1 : (AdeleRing (𝓞 ℚ) ℚ)ˣ) * 1) = ideleNorm ℚ 1 * ideleNorm ℚ 1 :=
          ideleNorm_mul ..
        rw [mul_one] at hm
        exact (mul_right_cancel₀ hp.ne' (by rw [one_mul]; exact hm)).symm
      have hdet : ideleNorm ℚ (Matrix.GeneralLinearGroup.det (((n * u : Gf)) : AdelicGL2 (𝓞 ℚ) ℚ)) = 1 := by
        rw [Subgroup.coe_mul, map_mul, ideleNorm_mul, hUdet u hu, mul_one, det_of_mem_finUnipotent hn, h1]
      rw [hP, hdet, Complex.ofReal_one, Complex.one_cpow, mul_one]
    · rw [Set.indicator_of_notMem hg]
      have hP : W g * F g = 0 := by
        by_contra h
        obtain ⟨n, u, hu, rfl⟩ := hsupp g h
        exact hg (Set.mul_mem_mul n.2 hu)
      rw [hP, zero_mul]
  unfold RSCarrier.rsFinIntegral RSCarrier.rsLocalIntegral
  simp_rw [hpt]
  rw [integral_indicator_const _ hEo.measurableSet, Complex.real_smul, measureReal_def]

end Ws23Support

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

theorem solution
    [SecondCountableTopology (AdelicGL2 (𝓞 ℚ) ℚ)]
    (μ : Measure (finiteAdelicGL2Subgroup ℚ)) [μ.IsHaarMeasure]
    (μN : Measure RSCarrier.finUnipotent) [μN.IsHaarMeasure]
    (U : Subgroup (finiteAdelicGL2Subgroup ℚ))
    (hUc : IsCompact (U : Set (finiteAdelicGL2Subgroup ℚ)))
    (hUo : IsOpen (U : Set (finiteAdelicGL2Subgroup ℚ)))
    (hUdet : ∀ u ∈ U, ideleNorm ℚ (Matrix.GeneralLinearGroup.det ((u : finiteAdelicGL2Subgroup ℚ) : AdelicGL2 (𝓞 ℚ) ℚ)) = 1) :
    ∃ c : ℝ, 0 < c ∧
      ∀ (s : ℂ) (W F : finiteAdelicGL2Subgroup ℚ → ℂ),
        (∀ (n : RSCarrier.finUnipotent) (g : finiteAdelicGL2Subgroup ℚ),
          W ((n : finiteAdelicGL2Subgroup ℚ) * g) * F ((n : finiteAdelicGL2Subgroup ℚ) * g) = W g * F g) →
        (∀ g : finiteAdelicGL2Subgroup ℚ, W g * F g ≠ 0 →
          ∃ (n : RSCarrier.finUnipotent) (u : finiteAdelicGL2Subgroup ℚ), u ∈ U ∧
            g = (n : finiteAdelicGL2Subgroup ℚ) * u) →
        (∀ u ∈ U, W u * F u = W 1 * F 1) →
        RSCarrier.rsFinIntegral μ μN s W F = (c : ℂ) * (W 1 * F 1) :=
  Ws23Support.main μ μN U hUc hUo hUdet

end S_LanglandsTunnell_RankinSelberg_exists_pos_forall_rsFinIntegral_eq_mul_of_support_subset_unipotent_mul
end P2MW
export P2MW.S_LanglandsTunnell_RankinSelberg_exists_pos_forall_rsFinIntegral_eq_mul_of_support_subset_unipotent_mul (solution)
