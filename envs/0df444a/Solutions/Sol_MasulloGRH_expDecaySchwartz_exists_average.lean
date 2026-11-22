-- Prove2me | solution 1 for MasulloGRH.expDecaySchwartz_exists_average
-- status  : ACCEPTED   (prove)
-- author  : @sflicht
-- created : 2026-11-21T19:18:28.006438+00:00
-- url     : https://prove2.me/submissions/a2e83db2-e35e-4901-b057-21ff88607966

import Theorems.Thm_MasulloGRH_schwartzBruhat_average_mem
import Theorems.Thm_MasulloGRH_schwartzBruhat_pushforward_quotient
import Theorems.Thm_MasulloGRH_expDecayStage_weighted_mem
import Theorems.Thm_MasulloGRH_isCompact_of_isGoodSubgroup
import Theorems.Thm_MasulloGRH_isCompact_moduleKernel_and_compact_le

set_option autoImplicit false

namespace AvgAux

open MasulloGRH MeasureTheory

variable {H : Type*} [CommGroup H] [TopologicalSpace H] [IsTopologicalGroup H] [T2Space H]

lemma avg_eq_haar (k : Subgroup H) (hk : IsCompact (k : Set H)) (F : H → ℂ) (x : H) :
    letI : MeasurableSpace k := borel k
    haveI : BorelSpace k := ⟨rfl⟩
    haveI : CompactSpace k := isCompact_iff_compactSpace.mp hk
    schwartzBruhatAverage ⊤ k F x = ∫ y : k, F (x * y) ∂(Measure.haarMeasure ⊤) := by
  letI : MeasurableSpace k := borel k
  haveI : BorelSpace k := ⟨rfl⟩
  haveI : CompactSpace k := isCompact_iff_compactSpace.mp hk
  unfold schwartzBruhatAverage
  rw [Set.indicator_of_mem (by simp : x ∈ ((⊤ : Subgroup H) : Set H))]
  have h2 : subgroupHaar k = Measure.haarMeasure ⊤ := by
    unfold subgroupHaar
    rw [dif_pos hk]
  rw [h2]

lemma avg_add (k : Subgroup H) (hk : IsCompact (k : Set H)) (F₁ F₂ : H → ℂ)
    (h₁ : Continuous F₁) (h₂ : Continuous F₂) (x : H) :
    schwartzBruhatAverage ⊤ k (F₁ + F₂) x =
      schwartzBruhatAverage ⊤ k F₁ x + schwartzBruhatAverage ⊤ k F₂ x := by
  letI : MeasurableSpace k := borel k
  haveI : BorelSpace k := ⟨rfl⟩
  haveI : CompactSpace k := isCompact_iff_compactSpace.mp hk
  rw [avg_eq_haar k hk, avg_eq_haar k hk, avg_eq_haar k hk]
  have hi : ∀ F : H → ℂ, Continuous F →
      Integrable (fun y : k => F (x * y)) (Measure.haarMeasure ⊤) := by
    intro F hF
    have hc : Continuous (fun y : k => F (x * y)) :=
      hF.comp (continuous_const.mul continuous_subtype_val)
    exact integrableOn_univ.1 (hc.continuousOn.integrableOn_compact isCompact_univ)
  simp only [Pi.add_apply]
  exact integral_add (hi F₁ h₁) (hi F₂ h₂)

lemma avg_mul_left (k : Subgroup H) (w F : H → ℂ) (x : H)
    (hw : ∀ y ∈ k, w (x * y) = w x) :
    schwartzBruhatAverage ⊤ k (fun z => w z * F z) x = w x * schwartzBruhatAverage ⊤ k F x := by
  letI : MeasurableSpace k := borel k
  unfold schwartzBruhatAverage
  rw [Set.indicator_of_mem (by simp : x ∈ ((⊤ : Subgroup H) : Set H)),
    Set.indicator_of_mem (by simp : x ∈ ((⊤ : Subgroup H) : Set H))]
  have : (fun y : k => w (x * y) * F (x * y)) = fun y : k => w x * F (x * y) :=
    funext fun y => by rw [hw y y.2]
  simp only [this]
  exact integral_const_mul _ _

lemma avg_smul (k : Subgroup H) (c : ℂ) (F : H → ℂ) (x : H) :
    schwartzBruhatAverage ⊤ k (c • F) x = c * schwartzBruhatAverage ⊤ k F x :=
  avg_mul_left k (fun _ => c) F x (fun _ _ => rfl)

lemma avg_congr (k : Subgroup H) (F F' : H → ℂ) (x : H)
    (h : ∀ y ∈ k, F (x * y) = F' (x * y)) :
    schwartzBruhatAverage ⊤ k F x = schwartzBruhatAverage ⊤ k F' x := by
  letI : MeasurableSpace k := borel k
  unfold schwartzBruhatAverage
  rw [Set.indicator_of_mem (by simp : x ∈ ((⊤ : Subgroup H) : Set H)),
    Set.indicator_of_mem (by simp : x ∈ ((⊤ : Subgroup H) : Set H))]
  have : (fun y : k => F (x * y)) = fun y : k => F' (x * y) := funext fun y => h y y.2
  simp only [this]

lemma avg_mul_inv (k : Subgroup H) (hk : IsCompact (k : Set H)) (F : H → ℂ) (x h : H)
    (hh : h ∈ k) :
    schwartzBruhatAverage ⊤ k F (x * h) = schwartzBruhatAverage ⊤ k F x := by
  letI : MeasurableSpace k := borel k
  haveI : BorelSpace k := ⟨rfl⟩
  haveI : CompactSpace k := isCompact_iff_compactSpace.mp hk
  rw [avg_eq_haar k hk, avg_eq_haar k hk]
  have := integral_mul_left_eq_self (μ := Measure.haarMeasure (⊤ : TopologicalSpace.PositiveCompacts k))
    (fun y : k => F (x * y)) (⟨h, hh⟩ : k)
  rw [← this]
  congr 1
  funext y
  simp [mul_assoc]

lemma avg_continuous (k : Subgroup H) (hk : IsCompact (k : Set H)) [LocallyCompactSpace H] [FirstCountableTopology H]
    (F : H → ℂ) (hF : Continuous F) : Continuous (schwartzBruhatAverage ⊤ k F) := by
  letI : MeasurableSpace k := borel k
  haveI : BorelSpace k := ⟨rfl⟩
  haveI : CompactSpace k := isCompact_iff_compactSpace.mp hk
  have : schwartzBruhatAverage ⊤ k F = fun x => ∫ y : k, F (x * y) ∂(Measure.haarMeasure ⊤) :=
    funext fun x => avg_eq_haar k hk F x
  rw [this]
  have hc : Continuous (Function.uncurry fun (x : H) (y : k) => F (x * y)) :=
    hF.comp (continuous_fst.mul (continuous_subtype_val.comp continuous_snd))
  have := continuous_parametric_integral_of_continuous (μ := Measure.haarMeasure
    (⊤ : TopologicalSpace.PositiveCompacts k)) hc isCompact_univ
  simpa [Measure.restrict_univ] using this

/-- the kernel of a module as a subgroup -/
def modKer {G : Type*} [CommGroup G] [TopologicalSpace G] {m : G → ℝ} (hm : IsModule m) : Subgroup G where
  carrier := {g | m g = 1}
  one_mem' := by
    show m 1 = 1
    have h := hm.map_mul 1 1
    rw [mul_one] at h
    have hp := hm.pos 1
    nlinarith
  mul_mem' {a b} ha hb := by
    show m (a * b) = 1
    rw [hm.map_mul, show m a = 1 from ha, show m b = 1 from hb, one_mul]
  inv_mem' {a} ha := by
    show m a⁻¹ = 1
    have h := hm.map_mul a a⁻¹
    rw [mul_inv_cancel, show m a = 1 from ha, one_mul] at h
    have h1 := hm.map_mul 1 1
    rw [mul_one] at h1
    have hp := hm.pos 1
    have : m 1 = 1 := by nlinarith
    rw [← h, this]

end AvgAux

universe u

open MasulloGRH AvgAux MeasureTheory in
theorem solution
    (G : Type u) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [LocallyCompactSpace G] [SecondCountableTopology G] (m : G → ℝ) (hm : IsRposModule m)
    (I : Set ℝ) (hI : I.OrdConnected) (hne : I.Nonempty) (k : Subgroup G) (hk : IsGoodSubgroup k) :
    ∃ A : ExpDecaySchwartz G m I →ₗ[ℂ] ExpDecayStage G m I k,
      (∀ y, A (ExpDecayStage.incl G m I k y) = y) ∧
      ∀ k' : Subgroup G, IsGoodSubgroup k' →
        Continuous (fun y : ExpDecayStage G m I k' => A (ExpDecayStage.incl G m I k' y)) := by
  have hkc : IsCompact (k : Set G) := isCompact_of_isGoodSubgroup G k hk
  have hm1 : ∀ (c : Subgroup G), IsGoodSubgroup c → ∀ h ∈ c, m h = 1 := by
    intro c hc h hh
    exact (isCompact_moduleKernel_and_compact_le G m hm (modKer hm.1) (fun g => Iff.rfl)).2
      c (isCompact_of_isGoodSubgroup G c hc) hh
  let av : (G → ℂ) → G → ℂ := schwartzBruhatAverage ⊤ k
  -- elements of `S_I(G)` are continuous
  have hcont : ∀ φ ∈ expDecaySubmodule G m I, Continuous φ := by
    intro φ hφ
    induction hφ using Submodule.span_induction with
    | mem φ hφ => exact hφ.1
    | zero => exact continuous_const
    | add φ ψ _ _ h₁ h₂ => exact h₁.add h₂
    | smul c φ _ h => exact continuous_const.mul h
  -- averaging preserves `S_I(G)`
  have hmem : ∀ φ ∈ expDecaySubmodule G m I, av φ ∈ expDecaySubmodule G m I := by
    intro φ hφ
    induction hφ using Submodule.span_induction with
    | mem φ hφ =>
      refine Submodule.subset_span ⟨avg_continuous k hkc φ hφ.1, fun a ha => ?_⟩
      have : (fun g => ((m g ^ a : ℝ) : ℂ) * av φ g) =
          av (fun g => ((m g ^ a : ℝ) : ℂ) * φ g) := by
        funext g
        refine (avg_mul_left k (fun g => ((m g ^ a : ℝ) : ℂ)) φ g fun y hy => ?_).symm
        simp only [hm.1.map_mul, hm1 k hk y hy, mul_one]
      rw [this]
      exact schwartzBruhat_average_mem G k hk _ (hφ.2 a ha)
    | zero =>
      have : av 0 = 0 := by
        funext g
        have := avg_smul k 0 (0 : G → ℂ) g
        simpa using this
      rw [this]; exact Submodule.zero_mem _
    | add φ ψ hφ hψ h₁ h₂ =>
      have : av (φ + ψ) = av φ + av ψ :=
        funext fun g => avg_add k hkc φ ψ (hcont φ hφ) (hcont ψ hψ) g
      rw [this]; exact Submodule.add_mem _ h₁ h₂
    | smul c φ _ h =>
      have : av (c • φ) = c • av φ := funext fun g => avg_smul k c φ g
      rw [this]; exact Submodule.smul_mem _ c h
  let A : ExpDecaySchwartz G m I →ₗ[ℂ] ExpDecayStage G m I k :=
    { toFun := fun φ => ⟨⟨av φ.1, hmem φ.1 φ.2⟩, fun h hh g => avg_mul_inv k hkc φ.1 g h hh⟩
      map_add' := fun φ ψ => by
        apply Subtype.ext; apply Subtype.ext
        exact funext fun g => avg_add k hkc φ.1 ψ.1 (hcont _ φ.2) (hcont _ ψ.2) g
      map_smul' := fun c φ => by
        apply Subtype.ext; apply Subtype.ext
        exact funext fun g => avg_smul k c φ.1 g }
  refine ⟨A, fun y => ?_, fun k' hk' => ?_⟩
  · apply Subtype.ext; apply Subtype.ext
    funext g
    show schwartzBruhatAverage ⊤ k y.1.1 g = y.1.1 g
    letI : MeasurableSpace k := borel k
    haveI : BorelSpace k := ⟨rfl⟩
    haveI : CompactSpace k := isCompact_iff_compactSpace.mp hkc
    rw [avg_eq_haar k hkc]
    have h1 : (fun z : k => y.1.1 (g * z)) = fun _ => y.1.1 g := funext fun z => y.2 z z.2 g
    simp only [h1, integral_const]
    have h3 : (Measure.haarMeasure (⊤ : TopologicalSpace.PositiveCompacts k)) Set.univ = 1 := by
      have := Measure.haarMeasure_self (K₀ := (⊤ : TopologicalSpace.PositiveCompacts k))
      simpa using this
    simp [measureReal_def, h3]
  · obtain ⟨Q, hQ⟩ := schwartzBruhat_pushforward_quotient G k k' hk hk'
    refine continuous_iInf_rng.2 fun a => continuous_iInf_rng.2 fun ha =>
      continuous_induced_rng.2 ?_
    have hcont' : Continuous (fun y : ExpDecayStage G m I k' =>
        ExpDecaySchwartz.weighted k' a y.1) := continuous_iff_le_induced.2 (iInf₂_le a ha)
    have hwf : ∀ (c : Subgroup G) (hc : IsGoodSubgroup c) (y : ExpDecayStage G m I c),
        (ExpDecaySchwartz.weighted c a y.1).toFun =
          fun x : G ⧸ c => ((m x.out ^ a : ℝ) : ℂ) * y.1.toFun x.out := by
      intro c hc y
      have hmem := expDecayStage_weighted_mem G m hm I hI hne c hc y a ha
      unfold ExpDecaySchwartz.weighted
      first
        | (erw [dif_pos hmem]; rfl)
        | (simp only [hmem, dif_pos]; rfl)
        | (split <;> [rfl; exact absurd hmem ‹_›])
    have heq : ∀ y : ExpDecayStage G m I k',
        ExpDecaySchwartz.weighted k a (A (ExpDecayStage.incl G m I k' y)).1 =
          Q (ExpDecaySchwartz.weighted k' a y.1) := by
      intro y
      apply Subtype.ext
      show (ExpDecaySchwartz.weighted k a (A (ExpDecayStage.incl G m I k' y)).1).toFun =
        (Q (ExpDecaySchwartz.weighted k' a y.1)).toFun
      rw [hwf k hk]
      funext x
      rw [hQ, hwf k' hk' y]
      show ((m x.out ^ a : ℝ) : ℂ) * av y.1.1 x.out = _
      rw [← avg_mul_left k (fun g => ((m g ^ a : ℝ) : ℂ)) y.1.1 x.out (fun z hz => by
        simp only [hm.1.map_mul, hm1 k hk z hz, mul_one])]
      refine avg_congr k _ _ x.out fun z _ => ?_
      obtain ⟨h', hh'⟩ := QuotientGroup.mk_out_eq_mul k' (x.out * z)
      show _ = ((m (QuotientGroup.mk (x.out * z) : G ⧸ k').out ^ a : ℝ) : ℂ) *
        y.1.toFun (QuotientGroup.mk (x.out * z) : G ⧸ k').out
      rw [hh']
      rw [show m (x.out * z * h') = m (x.out * z) by rw [hm.1.map_mul, hm1 k' hk' h' h'.2, mul_one]]
      rw [show y.1.toFun (x.out * z * h') = y.1.toFun (x.out * z) from y.2 h' h'.2 _]
      rfl
    exact (Q.continuous.comp hcont').congr fun y => (heq y).symm
