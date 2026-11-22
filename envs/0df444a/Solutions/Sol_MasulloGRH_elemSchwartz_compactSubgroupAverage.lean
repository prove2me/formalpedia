-- Prove2me | solution 1 for MasulloGRH.elemSchwartz_compactSubgroupAverage
-- status  : ACCEPTED   (prove)
-- author  : @sflicht
-- created : 2026-11-21T17:15:45.108176+00:00
-- url     : https://prove2.me/submissions/07d876a7-40bd-482f-81e2-9659f561acd0

import Theorems.Thm_MasulloGRH_elemSchwartz_torusAverage
import Theorems.Thm_MasulloGRH_isRapidDecay_elemSchwartz_toFun
import Theorems.Thm_MasulloGRH_elemSchwartz_continuous_of_seminorm_bound
import Definitions.Def_MasulloGRH_SchwartzBruhatAveraging

set_option autoImplicit false

open MeasureTheory Topology Filter

namespace MasulloGRHCAvgAux

open MasulloGRH

variable {m n r s : ℕ} {d : Fin s → ℕ}

/-! ### translation in the finite factor -/

def trF (f : (i : Fin s) → ZMod (d i)) (g : ElemGroup m n r s d → ℂ) : ElemGroup m n r s d → ℂ :=
  fun e => g (e.1, e.2.1, e.2.2.1, e.2.2.2 + f)

lemma isRapidDecay_trF (f : (i : Fin s) → ZMod (d i)) {g : ElemGroup m n r s d → ℂ}
    (hg : IsRapidDecay g) : IsRapidDecay (trF f g) :=
  ⟨fun a b => hg.1 a (b + f), fun i j k => by
    obtain ⟨C, hC⟩ := hg.2 i j k
    exact ⟨C, fun a b xt => hC a (b + f) xt⟩⟩

noncomputable def trLin (f : (i : Fin s) → ZMod (d i)) :
    ElemSchwartz m n r s d →ₗ[ℂ] ElemSchwartz m n r s d where
  toFun g := ⟨trF f g.toFun,
    Submodule.subset_span (isRapidDecay_trF f (isRapidDecay_elemSchwartz_toFun g))⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

lemma continuous_trLin (f : (i : Fin s) → ZMod (d i)) :
    Continuous (trLin (m := m) (n := n) (r := r) f) :=
  elemSchwartz_continuous_of_seminorm_bound (trLin (m := m) (n := n) (r := r) f).toAddMonoidHom
    (fun p => ⟨{p}, 1, fun g M hM a b xt => by
      rw [one_mul]
      exact hM p (Finset.mem_singleton_self p) a (b + f) xt⟩)

/-! ### compact subgroups lie in `0 × 𝕋^n × 0 × F` -/

variable {C : Subgroup (Multiplicative (ElemGroup m n r s d))}

lemma fst_eq_zero (hC : IsCompact (C : Set (Multiplicative (ElemGroup m n r s d))))
    {c : Multiplicative (ElemGroup m n r s d)} (hc : c ∈ C) : (Multiplicative.toAdd c).1 = 0 := by
  obtain ⟨R, hR⟩ := (hC.image (continuous_fst.comp continuous_toAdd)).isBounded.exists_norm_le
  by_contra hv
  obtain ⟨i, hi⟩ : ∃ i, (Multiplicative.toAdd c).1 i ≠ 0 := by
    by_contra h; push Not at h; exact hv (funext h)
  have hpos : 0 < |(Multiplicative.toAdd c).1 i| := abs_pos.2 hi
  obtain ⟨N, hN⟩ := exists_nat_gt (R / |(Multiplicative.toAdd c).1 i|)
  have h1 := hR _ ⟨c ^ N, C.pow_mem hc N, rfl⟩
  simp only [Function.comp_apply, toAdd_pow, Prod.smul_fst] at h1
  have h2 := norm_le_pi_norm (N • (Multiplicative.toAdd c).1) i
  rw [Pi.smul_apply, nsmul_eq_mul, Real.norm_eq_abs, abs_mul, Nat.abs_cast] at h2
  rw [div_lt_iff₀ hpos] at hN
  linarith

lemma int_eq_zero (hC : IsCompact (C : Set (Multiplicative (ElemGroup m n r s d))))
    {c : Multiplicative (ElemGroup m n r s d)} (hc : c ∈ C) :
    (Multiplicative.toAdd c).2.2.1 = 0 := by
  obtain ⟨R, hR⟩ := (hC.image ((continuous_fst.comp (continuous_snd.comp continuous_snd)).comp
    continuous_toAdd)).isBounded.exists_norm_le
  by_contra hv
  obtain ⟨i, hi⟩ : ∃ i, (Multiplicative.toAdd c).2.2.1 i ≠ 0 := by
    by_contra h; push Not at h; exact hv (funext h)
  have hpos : (1 : ℝ) ≤ |((Multiplicative.toAdd c).2.2.1 i : ℝ)| := by
    rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hi
  obtain ⟨N, hN⟩ := exists_nat_gt R
  have h1 := hR _ ⟨c ^ N, C.pow_mem hc N, rfl⟩
  simp only [Function.comp_apply, toAdd_pow, Prod.smul_snd, Prod.smul_fst] at h1
  have h2 := norm_le_pi_norm (N • (Multiplicative.toAdd c).2.2.1) i
  rw [Pi.smul_apply, nsmul_eq_mul, Int.norm_eq_abs, Int.cast_mul, abs_mul, Int.cast_natCast,
    Nat.abs_cast] at h2
  nlinarith

/-! ### slices of rapid-decay functions -/

lemma bdd {g : ElemGroup m n r s d → ℂ} (hg : IsRapidDecay g) :
    ∃ C : ℝ, ∀ e, ‖g e‖ ≤ C := by
  obtain ⟨C, hC⟩ := hg.2 0 0 0
  refine ⟨C, fun e => ?_⟩
  obtain ⟨x, z, a, b⟩ := e
  have h := hC a b (x, fun j => (z j).out)
  simp only [pow_zero, one_mul, norm_iteratedFDeriv_zero] at h
  have he : elemLift g a b (x, fun j => (z j).out) = g (x, z, a, b) := by
    simp only [elemLift]
    congr
    funext j
    exact QuotientAddGroup.out_eq' (z j)
  rwa [he] at h

lemma cont_slice {g : ElemGroup m n r s d → ℂ} (hg : IsRapidDecay g) (x : Fin m → ℝ)
    (z : Fin n → UnitAddCircle) (a : Fin r → ℤ) (b : (i : Fin s) → ZMod (d i)) :
    Continuous (fun v : Fin n → ℝ => g (x, z + (fun j => ((v j : ℝ) : UnitAddCircle)), a, b)) := by
  have he : (fun v : Fin n → ℝ => g (x, z + (fun j => ((v j : ℝ) : UnitAddCircle)), a, b)) =
      fun v => elemLift g a b (x, (fun j => (z j).out) + v) := by
    funext v
    simp only [elemLift, Pi.add_apply, AddCircle.coe_add]
    congr
    funext j
    rw [QuotientAddGroup.out_eq' (z j)]
  rw [he]
  exact (hg.1 a b).continuous.comp (continuous_const.prodMk (continuous_const.add continuous_id))

/-! ### the integral over a compact subgroup -/

noncomputable def L (z : UnitAddCircle) : ℝ := ((AddCircle.equivIco 1 0 z : Set.Ico (0 : ℝ) (0 + 1)) : ℝ)

lemma coe_L (z : UnitAddCircle) : ((L z : ℝ) : UnitAddCircle) = z := AddCircle.coe_equivIco

lemma measurable_L : Measurable L :=
  measurable_subtype_coe.comp (AddCircle.measurableEquivIco 1 0).measurable

def cv (c : C) : ElemGroup m n r s d := Multiplicative.toAdd (c : Multiplicative (ElemGroup m n r s d))

noncomputable def τ (c : C) : Fin n → ℝ := fun j => L ((cv c).2.1 j)

def S (f : (i : Fin s) → ZMod (d i)) : Set C := (fun c => (cv c).2.2.2) ⁻¹' {f}

variable [MeasurableSpace C] [BorelSpace C]

lemma measurable_τ : Measurable (τ (C := C)) :=
  measurable_pi_lambda _ fun j => measurable_L.comp
    ((continuous_apply j).comp ((continuous_fst.comp continuous_snd).comp
      (continuous_toAdd.comp continuous_subtype_val))).measurable

lemma measurableSet_S (f : (i : Fin s) → ZMod (d i)) : MeasurableSet (S (C := C) f) :=
  (isClosed_singleton.preimage ((continuous_snd.comp (continuous_snd.comp continuous_snd)).comp
    (continuous_toAdd.comp continuous_subtype_val))).measurableSet

lemma decomp (hC : IsCompact (C : Set (Multiplicative (ElemGroup m n r s d))))
    (e : ElemGroup m n r s d) (c : C) :
    e + cv c =
      (e.1, e.2.1 + (fun j => ((τ c j : ℝ) : UnitAddCircle)), e.2.2.1,
        e.2.2.2 + (cv c).2.2.2) := by
  have h1 : (cv c).1 = 0 := fst_eq_zero hC c.2
  have h2 : (cv c).2.2.1 = 0 := int_eq_zero hC c.2
  ext
  · simp [h1]
  · simp [τ, coe_L]
  · simp [h2]
  · rfl

lemma integral_eq [Fintype ((i : Fin s) → ZMod (d i))]
    (hC : IsCompact (C : Set (Multiplicative (ElemGroup m n r s d))))
    (μ : Measure C) [IsFiniteMeasure μ] {g : ElemGroup m n r s d → ℂ} (hg : IsRapidDecay g)
    (e : ElemGroup m n r s d) :
    ∫ c, g (e + cv c) ∂μ =
      ∑ f, ∫ v, g (e.1, e.2.1 + (fun j => ((v j : ℝ) : UnitAddCircle)), e.2.2.1, e.2.2.2 + f)
        ∂((μ.restrict (S f)).map τ) := by
  set G : ((i : Fin s) → ZMod (d i)) → (Fin n → ℝ) → ℂ := fun f v =>
    g (e.1, e.2.1 + (fun j => ((v j : ℝ) : UnitAddCircle)), e.2.2.1, e.2.2.2 + f) with hG
  have hGc : ∀ f, Continuous (G f) := fun f => cont_slice hg _ _ _ _
  obtain ⟨B, hB⟩ := bdd hg
  have hpt : ∀ c : C, g (e + cv c) =
      ∑ f, (S f).indicator (fun c => G f (τ c)) c := by
    intro c
    rw [Finset.sum_eq_single (cv c).2.2.2]
    · rw [Set.indicator_of_mem (show c ∈ S _ from rfl), decomp hC e c]
    · intro f _ hf
      exact Set.indicator_of_notMem (fun h => hf h.symm) _
    · intro h; exact absurd (Finset.mem_univ _) h
  have hint : ∀ f, Integrable (fun c => G f (τ c)) μ := fun f =>
    Integrable.of_bound ((hGc f).measurable.comp measurable_τ).aestronglyMeasurable B
      (Eventually.of_forall fun c => hB _)
  rw [integral_congr_ae (Eventually.of_forall hpt), integral_finsetSum _ fun f _ =>
    (hint f).indicator (measurableSet_S f)]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [integral_indicator (measurableSet_S f),
    integral_map measurable_τ.aemeasurable (hGc f).aestronglyMeasurable]

omit [MeasurableSpace C] [BorelSpace C] in
theorem continuousAdd_elemSchwartz : ContinuousAdd (ElemSchwartz m n r s d) := by
  let φ : ElemSchwartz m n r s d →+ ((p : ℕ × ℕ × ℕ) →
      UniformFun ((Fin r → ℤ) × ((i : Fin s) → ZMod (d i)) × ((Fin m → ℝ) × (Fin n → ℝ)))
        (ContinuousMultilinearMap ℝ (fun _ : Fin p.2.2 => (Fin m → ℝ) × (Fin n → ℝ)) ℂ)) :=
    { toFun := fun g p => UniformFun.ofFun
        (fun q => (‖q.1‖ ^ p.2.1 * ‖q.2.2.1‖ ^ p.1) •
          iteratedFDeriv ℝ p.2.2 (elemLift g.toFun q.1 q.2.1) q.2.2)
      map_zero' := by
        funext p
        have h0 : ∀ a b, elemLift (0 : ElemSchwartz m n r s d).toFun a b = fun _ => 0 :=
          fun a b => rfl
        simp only [h0, iteratedFDeriv_fun_zero, Pi.zero_apply, smul_zero]
        rfl
      map_add' := fun g h => by
        funext p
        have h0 : ∀ a b, elemLift (g + h).toFun a b = elemLift g.toFun a b + elemLift h.toFun a b :=
          fun a b => rfl
        have hk : ∀ a b xt, iteratedFDeriv ℝ p.2.2 (elemLift (g + h).toFun a b) xt =
            iteratedFDeriv ℝ p.2.2 (elemLift g.toFun a b) xt +
              iteratedFDeriv ℝ p.2.2 (elemLift h.toFun a b) xt := fun a b xt => by
          rw [h0, iteratedFDeriv_add_apply
            (((isRapidDecay_elemSchwartz_toFun g).1 a b).contDiffAt.of_le
              (by exact_mod_cast le_top))
            (((isRapidDecay_elemSchwartz_toFun h).1 a b).contDiffAt.of_le
              (by exact_mod_cast le_top))]
        simp only [hk, smul_add]
        rfl }
  exact continuousAdd_induced φ

omit [MeasurableSpace C] [BorelSpace C] in
lemma toFun_sum {ι : Type*} (t : Finset ι) (h : ι → ElemSchwartz m n r s d)
    (e : ElemGroup m n r s d) : (∑ i ∈ t, h i).toFun e = ∑ i ∈ t, (h i).toFun e := by
  let φ : ElemSchwartz m n r s d →+ (ElemGroup m n r s d → ℂ) :=
    { toFun := ElemSchwartz.toFun, map_zero' := rfl, map_add' := fun _ _ => rfl }
  have := map_sum φ h t
  rw [← Finset.sum_apply]
  exact congrFun this e

end MasulloGRHCAvgAux

namespace MasulloGRHCAvgAux

open MasulloGRH

theorem main {m n r s : ℕ} {d : Fin s → ℕ} (hd : ∀ i, d i ≠ 0)
    (C : Subgroup (Multiplicative (ElemGroup m n r s d))) :
    ∃ A : ElemSchwartz m n r s d →ₗ[ℂ] ElemSchwartz m n r s d, Continuous A ∧
      ∀ (g : ElemSchwartz m n r s d) (e : ElemGroup m n r s d),
        (A g).toFun e = (letI : MeasurableSpace C := borel C
          ∫ c : C, g.toFun (e + Multiplicative.toAdd (c : Multiplicative (ElemGroup m n r s d)))
            ∂ subgroupHaar C) := by
  letI : MeasurableSpace C := borel C
  haveI : BorelSpace C := ⟨rfl⟩
  by_cases hC : IsCompact (C : Set (Multiplicative (ElemGroup m n r s d)))
  · haveI : CompactSpace C := isCompact_iff_compactSpace.mp hC
    have hμ : subgroupHaar C = Measure.haarMeasure ⊤ := by
      unfold subgroupHaar
      rw [dif_pos hC]
    haveI : IsFiniteMeasure (subgroupHaar C) := by rw [hμ]; infer_instance
    haveI : ∀ i, NeZero (d i) := fun i => ⟨hd i⟩
    have hA := fun f : (i : Fin s) → ZMod (d i) => elemSchwartz_torusAverage (m := m) (r := r)
      (d := d) (((subgroupHaar C).restrict (S f)).map τ)
    choose A hAc hAe using hA
    refine ⟨∑ f, (A f).comp (trLin f), ?_, fun g e => ?_⟩
    · haveI := continuousAdd_elemSchwartz (m := m) (n := n) (r := r) (d := d)
      have he : ⇑(∑ f, (A f).comp (trLin f)) = fun g => ∑ f, (A f) (trLin f g) := by
        funext g; rw [LinearMap.sum_apply]; rfl
      rw [he]
      exact continuous_finsetSum _ fun f _ => (hAc f).comp (continuous_trLin f)
    · show _ = ∫ c : C, g.toFun (e + cv c) ∂ subgroupHaar C
      rw [integral_eq hC _ (isRapidDecay_elemSchwartz_toFun g) e, LinearMap.sum_apply, toFun_sum]
      refine Finset.sum_congr rfl fun f _ => ?_
      rw [LinearMap.comp_apply, hAe]
      rfl
  · have hμ : subgroupHaar C = 0 := by
      unfold subgroupHaar
      rw [dif_neg hC]
    refine ⟨0, continuous_const, fun g e => ?_⟩
    show (0 : ElemGroup m n r s d → ℂ) e = ∫ c : C, g.toFun (e + cv c) ∂ subgroupHaar C
    rw [hμ, integral_zero_measure]
    rfl

end MasulloGRHCAvgAux

open MeasureTheory MasulloGRH in
theorem solution {m n r s : ℕ} {d : Fin s → ℕ} (hd : ∀ i, d i ≠ 0)
    (C : Subgroup (Multiplicative (ElemGroup m n r s d))) :
    ∃ A : ElemSchwartz m n r s d →ₗ[ℂ] ElemSchwartz m n r s d, Continuous A ∧
      ∀ (g : ElemSchwartz m n r s d) (e : ElemGroup m n r s d),
        (A g).toFun e = (letI : MeasurableSpace C := borel C
          ∫ c : C, g.toFun (e + Multiplicative.toAdd (c : Multiplicative (ElemGroup m n r s d)))
            ∂ subgroupHaar C) :=
  MasulloGRHCAvgAux.main hd C
