-- Prove2me | solution 1 for MasulloGRH.adelicTheta_shift_tendstoUniformlyOn_isCompact
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T18:18:48.510867+00:00
-- url     : https://prove2.me/submissions/3887ec95-3d46-4afb-b10e-a311d4da1dbb

import Mathlib
import Definitions.Def_MasulloGRH_AdelicTheta
import Theorems.Thm_MasulloGRH_adelicSchwartz_range_eval_eq_schwartzBruhat
import Theorems.Thm_NumberField_AdelicBox_exists_denom_of_hasCompactSupport

open MeasureTheory NumberField IsDedekindDomain

set_option autoImplicit false

namespace Sol_MasulloGRH_adelicTheta_shift_tendstoUniformlyOn_isCompact

open MasulloGRH
open scoped Classical SchwartzMap

section rho
variable (F : Type*) [Field F] [NumberField F]


/-- `InfiniteAdeleRing.ringEquiv_mixedSpace` as a homeomorphism. -/
noncomputable def rhoH : InfiniteAdeleRing F ≃ₜ mixedEmbedding.mixedSpace F :=
  (Homeomorph.piEquivPiSubtypeProd (fun (v : InfinitePlace F) => InfinitePlace.IsReal v)
      (fun (v : InfinitePlace F) => v.Completion)).trans
    (Homeomorph.prodCongr
      (Homeomorph.piCongrRight
        (fun v => (InfinitePlace.Completion.isometryEquivRealOfIsReal v.2).toHomeomorph))
      ((Homeomorph.piCongrRight (fun v => (InfinitePlace.Completion.isometryEquivComplexOfIsComplex
          (InfinitePlace.not_isReal_iff_isComplex.1 v.2)).toHomeomorph)).trans
        (Homeomorph.piCongrLeft (Y := fun _ => ℂ)
          (Equiv.subtypeEquivRight (fun _ => InfinitePlace.not_isReal_iff_isComplex)))))

theorem rhoH_apply (x : InfiniteAdeleRing F) :
    rhoH F x = InfiniteAdeleRing.ringEquiv_mixedSpace F x := rfl

theorem continuous_rho : Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace F) := by
  have : (⇑(InfiniteAdeleRing.ringEquiv_mixedSpace F)) = ⇑(rhoH F) :=
    funext fun x => (rhoH_apply F x).symm
  rw [this]; exact (rhoH F).continuous

end rho

variable {F : Type*} [Field F] [NumberField F]

/-- A function on the adeles admits, on every compact set of pairs (idele, adele), a summable
majorant for the shifted dilated values over `F`. -/
def Good (φ : AdeleRing (𝓞 F) F → ℂ) : Prop :=
  ∀ Z : Set (IdeleGroup F × AdeleRing (𝓞 F) F), IsCompact Z →
    ∃ u : F → ℝ, Summable u ∧ ∀ p ∈ Z, ∀ ξ : F,
      ‖φ ((p.1 : AdeleRing (𝓞 F) F) * (algebraMap F (AdeleRing (𝓞 F) F) ξ + p.2))‖ ≤ u ξ

theorem good_zero : Good (0 : AdeleRing (𝓞 F) F → ℂ) := fun _ _ =>
  ⟨0, summable_zero, fun p _ ξ => by simp⟩

theorem good_add {φ ψ : AdeleRing (𝓞 F) F → ℂ} (hφ : Good φ) (hψ : Good ψ) :
    Good (φ + ψ) := by
  intro Z hZ
  obtain ⟨u, hu, hub⟩ := hφ Z hZ
  obtain ⟨v, hv, hvb⟩ := hψ Z hZ
  refine ⟨u + v, hu.add hv, fun p hp ξ => ?_⟩
  simp only [Pi.add_apply]
  exact (norm_add_le _ _).trans (add_le_add (hub p hp ξ) (hvb p hp ξ))

theorem good_smul (c : ℂ) {φ : AdeleRing (𝓞 F) F → ℂ} (hφ : Good φ) : Good (c • φ) := by
  intro Z hZ
  obtain ⟨u, hu, hub⟩ := hφ Z hZ
  refine ⟨fun ξ => ‖c‖ * u ξ, hu.mul_left _, fun p hp ξ => ?_⟩
  simp only [Pi.smul_apply, smul_eq_mul, norm_mul]
  exact mul_le_mul_of_nonneg_left (hub p hp ξ) (norm_nonneg c)

theorem summable_lattice (k : ℕ) (hk : Module.finrank ℤ (mixedEmbedding.integerLattice F) < k) :
    Summable (fun a : 𝓞 F => ((1 + ‖mixedEmbedding F (a : F)‖) ^ k)⁻¹) := by
  have hk0 : k ≠ 0 := by omega
  have h1 : Summable (fun z : mixedEmbedding.integerLattice F =>
      ‖z‖⁻¹ ^ k + (if z = 0 then (1:ℝ) else 0)) :=
    (ZLattice.summable_norm_pow_inv _ k hk).add (hasSum_ite_eq _ (1 : ℝ)).summable
  have h2 : Summable (fun z : mixedEmbedding.integerLattice F =>
      ((1 + ‖(z : mixedEmbedding.mixedSpace F)‖) ^ k)⁻¹) := by
    refine Summable.of_nonneg_of_le (fun z => by positivity) (fun z => ?_) h1
    by_cases hz : z = 0
    · rw [if_pos hz, hz]
      have : ((0 : mixedEmbedding.integerLattice F) : mixedEmbedding.mixedSpace F) = 0 := rfl
      rw [this, norm_zero, norm_zero, inv_zero, zero_pow hk0]
      norm_num
    · rw [if_neg hz, add_zero, inv_pow]
      have hpos : 0 < ‖z‖ := norm_pos_iff.2 hz
      have hz' : ‖z‖ = ‖(z : mixedEmbedding.mixedSpace F)‖ := rfl
      rw [← hz']
      exact inv_anti₀ (pow_pos hpos k) (pow_le_pow_left₀ (norm_nonneg _) (by linarith) k)
  have hmem : ∀ a : 𝓞 F, mixedEmbedding F (a : F) ∈ mixedEmbedding.integerLattice F := fun a =>
    LinearMap.mem_range.2 ⟨a, rfl⟩
  have hinj : Function.Injective
      (fun a : 𝓞 F => (⟨mixedEmbedding F (a : F), hmem a⟩ : mixedEmbedding.integerLattice F)) := by
    intro a b hab
    have h4 : mixedEmbedding F (a : F) = mixedEmbedding F (b : F) := congrArg Subtype.val hab
    have h5 : (a : F) = (b : F) := mixedEmbedding_injective F h4
    exact Subtype.ext h5
  have h3 := h2.comp_injective hinj
  exact h3

theorem summable_majorant (d : 𝓞 F) (hd : d ≠ 0) (k : ℕ)
    (hk : Module.finrank ℤ (mixedEmbedding.integerLattice F) < k) (M : ℝ) :
    Summable (Set.indicator {ξ : F | ∃ a : 𝓞 F, (d : F) * ξ = a}
      (fun ξ => M * ((1 + ‖mixedEmbedding F ((d : F) * ξ)‖) ^ k)⁻¹)) := by
  have hd' : (d : F) ≠ 0 := fun h => hd (by exact_mod_cast h)
  let g : 𝓞 F → F := fun a => (a : F) / d
  have hg : Function.Injective g := fun a b hab => by
    have : (a : F) = b := by
      have h2 := congrArg (fun t => t * (d : F)) hab
      simpa [g, div_mul_cancel₀ _ hd'] using h2
    exact Subtype.ext this
  rw [← hg.summable_iff]
  · have : (Set.indicator {ξ : F | ∃ a : 𝓞 F, (d : F) * ξ = a}
        (fun ξ => M * ((1 + ‖mixedEmbedding F ((d : F) * ξ)‖) ^ k)⁻¹)) ∘ g =
        fun a : 𝓞 F => M * ((1 + ‖mixedEmbedding F (a : F)‖) ^ k)⁻¹ := by
      funext a
      have hda : (d : F) * ((a : F) / d) = a := by field_simp
      show Set.indicator {ξ : F | ∃ a : 𝓞 F, (d : F) * ξ = a}
        (fun ξ => M * ((1 + ‖mixedEmbedding F ((d : F) * ξ)‖) ^ k)⁻¹) ((a : F) / d) = _
      rw [Set.indicator_of_mem (show ((a : F) / d) ∈ {ξ : F | ∃ a : 𝓞 F, (d : F) * ξ = a} from
        ⟨a, hda⟩), hda]
    rw [this]; exact (summable_lattice k hk).mul_left M
  · intro ξ hξ
    apply Set.indicator_of_notMem
    rintro ⟨a, ha⟩
    apply hξ
    refine ⟨a, ?_⟩
    show (a : F) / d = ξ
    rw [← ha]; field_simp

theorem good_pure (G : 𝓢(mixedEmbedding.mixedSpace F, ℂ)) (h : FiniteAdeleRing (𝓞 F) F → ℂ)
    (hlc : IsLocallyConstant h) (hcs : HasCompactSupport h) :
    Good (fun x : AdeleRing (𝓞 F) F =>
      G (InfiniteAdeleRing.ringEquiv_mixedSpace F x.1) * h x.2) := by
  intro Z hZ
  set ρ := InfiniteAdeleRing.ringEquiv_mixedSpace F with hρ
  have hcB : Continuous (fun p : IdeleGroup F × AdeleRing (𝓞 F) F =>
      ρ (((p.1⁻¹ : IdeleGroup F) : AdeleRing (𝓞 F) F).1)) :=
    (continuous_rho F).comp (continuous_fst.comp ((Units.continuous_coe_inv (M := AdeleRing (𝓞 F) F)).comp continuous_fst))
  obtain ⟨B, hB⟩ := (hZ.image hcB).isBounded.exists_norm_le
  have hcR : Continuous (fun p : IdeleGroup F × AdeleRing (𝓞 F) F => ρ p.2.1) :=
    (continuous_rho F).comp (continuous_fst.comp continuous_snd)
  obtain ⟨R, hR⟩ := (hZ.image hcR).isBounded.exists_norm_le
  let Φf : (IdeleGroup F × AdeleRing (𝓞 F) F) × FiniteAdeleRing (𝓞 F) F →
      FiniteAdeleRing (𝓞 F) F :=
    fun q => (((q.1.1⁻¹ : IdeleGroup F) : AdeleRing (𝓞 F) F).2) * q.2 - q.1.2.2
  have hΦf : Continuous Φf :=
    ((continuous_snd.comp ((Units.continuous_coe_inv (M := AdeleRing (𝓞 F) F)).comp (continuous_fst.comp continuous_fst))).mul
      continuous_snd).sub (continuous_snd.comp (continuous_snd.comp continuous_fst))
  set Kf := Φf '' (Z ×ˢ tsupport h) with hKf_def
  have hKf : IsCompact Kf := (hZ.prod hcs).image hΦf
  have hind : HasCompactSupport (Kf.indicator (fun _ => (1 : ℂ))) :=
    HasCompactSupport.intro hKf (fun x hx => Set.indicator_of_notMem hx _)
  obtain ⟨d, hd, hdK⟩ := NumberField.AdelicBox.exists_denom_of_hasCompactSupport hind
  have hden : ∀ ξ : F, algebraMap F (FiniteAdeleRing (𝓞 F) F) ξ ∈ Kf →
      ∃ a : 𝓞 F, (d : F) * ξ = a := by
    intro ξ hξ
    apply hdK
    rw [Set.indicator_of_mem hξ]; exact one_ne_zero
  obtain ⟨Ch, hCh⟩ := hlc.continuous.bounded_above_of_compact_support hcs
  have hCh0 : 0 ≤ Ch := (norm_nonneg _).trans (hCh 0)
  set k := Module.finrank ℤ (mixedEmbedding.integerLattice F) + 1 with hk_def
  obtain ⟨CG, hCG⟩ : ∃ CG : ℝ, ∀ y, ‖G y‖ ≤ CG * ((1 + ‖y‖) ^ k)⁻¹ := by
    refine ⟨2 ^ k * ((Finset.Iic (k, 0)).sup fun m => SchwartzMap.seminorm ℂ m.1 m.2) G,
      fun y => ?_⟩
    have := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℂ) (m := (k, 0)) (k := k) (n := 0)
      le_rfl le_rfl G y
    rw [norm_iteratedFDeriv_zero] at this
    have hpos : 0 < (1 + ‖y‖) ^ k := by positivity
    rw [← div_eq_mul_inv, le_div_iff₀ hpos, mul_comm]; exact this
  have hCG0 : 0 ≤ CG := by
    have := (norm_nonneg _).trans (hCG 0)
    simpa using this
  set D := max 1 ‖mixedEmbedding F (d : F)‖ * (1 + |R|) * max 1 B with hD_def
  have hD1 : 1 ≤ D := by
    have h1 : 1 ≤ max 1 ‖mixedEmbedding F (d : F)‖ := le_max_left _ _
    have h2 : 1 ≤ 1 + |R| := by have := abs_nonneg R; linarith
    have h3 : 1 ≤ max 1 B := le_max_left _ _
    calc (1 : ℝ) = 1 * 1 * 1 := by ring
      _ ≤ max 1 ‖mixedEmbedding F (d : F)‖ * (1 + |R|) * max 1 B := by gcongr
      _ = D := hD_def.symm
  refine ⟨_, summable_majorant d hd k (by omega) (CG * Ch * D ^ k), fun p hp ξ => ?_⟩
  have hnn : 0 ≤ Set.indicator {ξ : F | ∃ a : 𝓞 F, (d : F) * ξ = a}
      (fun ξ => CG * Ch * D ^ k * ((1 + ‖mixedEmbedding F ((d : F) * ξ)‖) ^ k)⁻¹) ξ :=
    Set.indicator_nonneg (fun _ _ => by positivity) _
  set y := (p.1 : AdeleRing (𝓞 F) F) * (algebraMap F (AdeleRing (𝓞 F) F) ξ + p.2) with hy_def
  by_cases hy : h y.2 = 0
  · show ‖G (ρ y.1) * h y.2‖ ≤ _
    rw [hy, mul_zero, norm_zero]; exact hnn
  have hm : y.2 ∈ tsupport h := subset_tsupport _ hy
  have hinv : ((p.1⁻¹ : IdeleGroup F) : AdeleRing (𝓞 F) F) * (p.1 : AdeleRing (𝓞 F) F) = 1 :=
    Units.inv_mul p.1
  have hy2 : y.2 = (p.1 : AdeleRing (𝓞 F) F).2 *
      (algebraMap F (FiniteAdeleRing (𝓞 F) F) ξ + p.2.2) := rfl
  have hξK : algebraMap F (FiniteAdeleRing (𝓞 F) F) ξ ∈ Kf := by
    refine ⟨(p, y.2), ⟨hp, hm⟩, ?_⟩
    have h2 : ((p.1⁻¹ : IdeleGroup F) : AdeleRing (𝓞 F) F).2 * (p.1 : AdeleRing (𝓞 F) F).2 = 1 :=
      congrArg Prod.snd hinv
    show ((p.1⁻¹ : IdeleGroup F) : AdeleRing (𝓞 F) F).2 * y.2 - p.2.2 = _
    rw [hy2, ← mul_assoc, h2, one_mul, add_sub_cancel_right]
  obtain ⟨a, ha⟩ := hden ξ hξK
  rw [Set.indicator_of_mem (show ξ ∈ {ξ : F | ∃ a : 𝓞 F, (d : F) * ξ = a} from ⟨a, ha⟩)]
  -- archimedean estimate
  set gi := ρ (((p.1⁻¹ : IdeleGroup F) : AdeleRing (𝓞 F) F).1) with hgi
  set gg := ρ ((p.1 : AdeleRing (𝓞 F) F).1) with hgg
  set v := mixedEmbedding F ξ + ρ p.2.1 with hv
  have hgigg : gi * gg = 1 := by
    rw [hgi, hgg, ← map_mul]
    have : (((p.1⁻¹ : IdeleGroup F) : AdeleRing (𝓞 F) F) * (p.1 : AdeleRing (𝓞 F) F)).1 =
        ((p.1⁻¹ : IdeleGroup F) : AdeleRing (𝓞 F) F).1 * (p.1 : AdeleRing (𝓞 F) F).1 := rfl
    rw [← this, hinv]; exact map_one ρ
  have hw : ρ y.1 = gg * v := by
    have : y.1 = (p.1 : AdeleRing (𝓞 F) F).1 * (algebraMap F (InfiniteAdeleRing F) ξ + p.2.1) :=
      rfl
    rw [this, map_mul, map_add, hv, InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp]
  set w := ρ y.1 with hw_def
  have hvw : v = gi * w := by rw [hw, ← mul_assoc, hgigg, one_mul]
  have hgiB : ‖gi‖ ≤ B := hB _ ⟨p, hp, rfl⟩
  have hRR : ‖ρ p.2.1‖ ≤ |R| := (hR _ ⟨p, hp, rfl⟩).trans (le_abs_self R)
  have hB0 : 0 ≤ B := (norm_nonneg _).trans hgiB
  have e1 : 1 + ‖v‖ ≤ max 1 B * (1 + ‖w‖) := by
    have : ‖v‖ ≤ B * ‖w‖ := by
      rw [hvw]; exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right hgiB (norm_nonneg _))
    have hm1 : B ≤ max 1 B := le_max_right _ _
    have hm2 : 1 ≤ max 1 B := le_max_left _ _
    nlinarith [norm_nonneg w]
  have e2 : 1 + ‖mixedEmbedding F ξ‖ ≤ (1 + |R|) * (1 + ‖v‖) := by
    have : ‖mixedEmbedding F ξ‖ ≤ ‖v‖ + |R| := by
      have : mixedEmbedding F ξ = v - ρ p.2.1 := by rw [hv]; abel
      rw [this]; exact (norm_sub_le _ _).trans (add_le_add_right hRR _)
    nlinarith [norm_nonneg v, abs_nonneg R]
  have e3 : 1 + ‖mixedEmbedding F ((d : F) * ξ)‖ ≤
      max 1 ‖mixedEmbedding F (d : F)‖ * (1 + ‖mixedEmbedding F ξ‖) := by
    rw [map_mul]
    have := norm_mul_le (mixedEmbedding F (d : F)) (mixedEmbedding F ξ)
    have hm1 : ‖mixedEmbedding F (d : F)‖ ≤ max 1 ‖mixedEmbedding F (d : F)‖ := le_max_right _ _
    have hm2 : (1 : ℝ) ≤ max 1 ‖mixedEmbedding F (d : F)‖ := le_max_left _ _
    nlinarith [norm_nonneg (mixedEmbedding F ξ)]
  have e4 : 1 + ‖mixedEmbedding F ((d : F) * ξ)‖ ≤ D * (1 + ‖w‖) := by
    have h1 : 0 ≤ max 1 ‖mixedEmbedding F (d : F)‖ := zero_le_one.trans (le_max_left _ _)
    have h2 : 0 ≤ 1 + |R| := by have := abs_nonneg R; linarith
    calc 1 + ‖mixedEmbedding F ((d : F) * ξ)‖
        ≤ max 1 ‖mixedEmbedding F (d : F)‖ * (1 + ‖mixedEmbedding F ξ‖) := e3
      _ ≤ max 1 ‖mixedEmbedding F (d : F)‖ * ((1 + |R|) * (1 + ‖v‖)) :=
          mul_le_mul_of_nonneg_left e2 h1
      _ ≤ max 1 ‖mixedEmbedding F (d : F)‖ * ((1 + |R|) * (max 1 B * (1 + ‖w‖))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left e1 h2) h1
      _ = D * (1 + ‖w‖) := by rw [hD_def]; ring
  have e5 : ((1 + ‖w‖) ^ k)⁻¹ ≤ D ^ k * ((1 + ‖mixedEmbedding F ((d : F) * ξ)‖) ^ k)⁻¹ := by
    have hpos1 : 0 < 1 + ‖mixedEmbedding F ((d : F) * ξ)‖ := by positivity
    have hpos2 : 0 < 1 + ‖w‖ := by positivity
    have hD0 : 0 < D := lt_of_lt_of_le zero_lt_one hD1
    have : (1 + ‖mixedEmbedding F ((d : F) * ξ)‖) ^ k ≤ D ^ k * (1 + ‖w‖) ^ k := by
      rw [← mul_pow]; exact pow_le_pow_left₀ hpos1.le e4 k
    rw [← div_eq_mul_inv, le_div_iff₀ (pow_pos hpos1 k)]
    calc ((1 + ‖w‖) ^ k)⁻¹ * (1 + ‖mixedEmbedding F ((d : F) * ξ)‖) ^ k
        ≤ ((1 + ‖w‖) ^ k)⁻¹ * (D ^ k * (1 + ‖w‖) ^ k) :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = D ^ k := by field_simp
  show ‖G w * h y.2‖ ≤ _
  rw [norm_mul]
  calc ‖G w‖ * ‖h y.2‖ ≤ (CG * ((1 + ‖w‖) ^ k)⁻¹) * Ch :=
        mul_le_mul (hCG w) (hCh _) (norm_nonneg _) (by positivity)
    _ ≤ (CG * (D ^ k * ((1 + ‖mixedEmbedding F ((d : F) * ξ)‖) ^ k)⁻¹)) * Ch := by
        gcongr
    _ = CG * Ch * D ^ k * ((1 + ‖mixedEmbedding F ((d : F) * ξ)‖) ^ k)⁻¹ := by ring


theorem good_and_cont {φ : AdeleRing (𝓞 F) F → ℂ}
    (hφ : φ ∈ NumberField.AdelicFourier.schwartzBruhat F) : Good φ ∧ Continuous φ := by
  refine NumberField.AdelicFourier.schwartzBruhat_induction
    (p := fun φ _ => Good φ ∧ Continuous φ) ?_ ?_ ?_ ?_ hφ
  · rintro f ⟨G, h, hlc, hcs, rfl⟩
    exact ⟨good_pure G h hlc hcs, (G.continuous.comp ((continuous_rho F).comp continuous_fst)).mul
      (hlc.continuous.comp continuous_snd)⟩
  · exact ⟨good_zero, continuous_const⟩
  · intro f g _ _ hf hg; exact ⟨good_add hf.1 hg.1, hf.2.add hg.2⟩
  · intro c f _ hf; exact ⟨good_smul c hf.1, hf.2.const_smul c⟩

end Sol_MasulloGRH_adelicTheta_shift_tendstoUniformlyOn_isCompact

open MasulloGRH Sol_MasulloGRH_adelicTheta_shift_tendstoUniformlyOn_isCompact

theorem solution
    (F : Type*) [Field F] [NumberField F] (f : AdelicSchwartz F) :
    (∀ p : IdeleGroup F × AdeleRing (𝓞 F) F,
      Summable (fun ξ : Fˣ =>
        ‖f.eval ((p.1 : AdeleRing (𝓞 F) F) *
          (algebraMap F (AdeleRing (𝓞 F) F) (ξ : F) + p.2))‖)) ∧
    (∀ Z : Set (IdeleGroup F × AdeleRing (𝓞 F) F), IsCompact Z →
      TendstoUniformlyOn
        (fun (s : Finset Fˣ) (p : IdeleGroup F × AdeleRing (𝓞 F) F) =>
          ∑ ξ ∈ s, ‖f.eval ((p.1 : AdeleRing (𝓞 F) F) *
            (algebraMap F (AdeleRing (𝓞 F) F) (ξ : F) + p.2))‖)
        (fun p : IdeleGroup F × AdeleRing (𝓞 F) F =>
          ∑' ξ : Fˣ, ‖f.eval ((p.1 : AdeleRing (𝓞 F) F) *
            (algebraMap F (AdeleRing (𝓞 F) F) (ξ : F) + p.2))‖)
        Filter.atTop Z) ∧
    Continuous (fun p : IdeleGroup F × AdeleRing (𝓞 F) F =>
      ∑' ξ : Fˣ, f.eval ((p.1 : AdeleRing (𝓞 F) F) *
        (algebraMap F (AdeleRing (𝓞 F) F) (ξ : F) + p.2))) ∧
    ∀ (g : IdeleGroup F) (x : AdeleRing (𝓞 F) F) (η : F),
      (∑' ξ : Fˣ, f.eval ((g : AdeleRing (𝓞 F) F) *
          (algebraMap F (AdeleRing (𝓞 F) F) (ξ : F) +
            (x + algebraMap F (AdeleRing (𝓞 F) F) η)))) +
        f.eval ((g : AdeleRing (𝓞 F) F) * (x + algebraMap F (AdeleRing (𝓞 F) F) η)) =
      (∑' ξ : Fˣ, f.eval ((g : AdeleRing (𝓞 F) F) *
          (algebraMap F (AdeleRing (𝓞 F) F) (ξ : F) + x))) +
        f.eval ((g : AdeleRing (𝓞 F) F) * x) := by
  classical
  have hf : f.eval ∈ NumberField.AdelicFourier.schwartzBruhat F := by
    have h' : f.eval ∈ Set.range (fun f : AdelicSchwartz F => f.eval) := ⟨f, rfl⟩
    rw [MasulloGRH.adelicSchwartz_range_eval_eq_schwartzBruhat F] at h'
    exact h'
  obtain ⟨hG, hC⟩ := good_and_cont hf
  have hU : ∀ Z : Set (IdeleGroup F × AdeleRing (𝓞 F) F), IsCompact Z →
      ∃ u : Fˣ → ℝ, Summable u ∧ ∀ (ξ : Fˣ), ∀ p ∈ Z,
        ‖f.eval ((p.1 : AdeleRing (𝓞 F) F) *
          (algebraMap F (AdeleRing (𝓞 F) F) (ξ : F) + p.2))‖ ≤ u ξ := by
    intro Z hZ
    obtain ⟨u, hu, hub⟩ := hG Z hZ
    exact ⟨fun ξ => u ξ, hu.comp_injective Units.val_injective, fun ξ p hp => hub p hp ξ⟩
  have hcont : ∀ ξ : Fˣ, Continuous (fun p : IdeleGroup F × AdeleRing (𝓞 F) F =>
      f.eval ((p.1 : AdeleRing (𝓞 F) F) *
        (algebraMap F (AdeleRing (𝓞 F) F) (ξ : F) + p.2))) := fun ξ =>
    hC.comp (((Units.continuous_val (M := AdeleRing (𝓞 F) F)).comp continuous_fst).mul
      (continuous_const.add continuous_snd))
  have hfull : ∀ (g : IdeleGroup F) (y : AdeleRing (𝓞 F) F),
      (∑' ξ : Fˣ, f.eval ((g : AdeleRing (𝓞 F) F) *
          (algebraMap F (AdeleRing (𝓞 F) F) (ξ : F) + y))) +
        f.eval ((g : AdeleRing (𝓞 F) F) * y) =
      ∑' ξ : F, f.eval ((g : AdeleRing (𝓞 F) F) *
          (algebraMap F (AdeleRing (𝓞 F) F) ξ + y)) := by
    intro g y
    obtain ⟨u, hu, hub⟩ := hG {(g, y)} isCompact_singleton
    have hs : Summable (fun ξ : F => f.eval ((g : AdeleRing (𝓞 F) F) *
        (algebraMap F (AdeleRing (𝓞 F) F) ξ + y))) :=
      Summable.of_norm_bounded hu (fun ξ => hub (g, y) rfl ξ)
    have hsupp : Function.support (fun n : F => if n = 0 then (0 : ℂ) else
        f.eval ((g : AdeleRing (𝓞 F) F) * (algebraMap F (AdeleRing (𝓞 F) F) n + y))) ⊆
        Set.range (Units.val : Fˣ → F) := by
      intro ξ hξ
      have h0 : ξ ≠ 0 := fun h0 => hξ (by simp only [if_pos h0])
      exact ⟨Units.mk0 ξ h0, rfl⟩
    have h2 := Units.val_injective.tsum_eq hsupp
    have h3 : (∑' ξ : Fˣ, f.eval ((g : AdeleRing (𝓞 F) F) *
          (algebraMap F (AdeleRing (𝓞 F) F) (ξ : F) + y))) =
        ∑' n : F, (if n = 0 then (0 : ℂ) else
          f.eval ((g : AdeleRing (𝓞 F) F) * (algebraMap F (AdeleRing (𝓞 F) F) n + y))) := by
      rw [← h2]
      exact tsum_congr fun ξ => by rw [if_neg ξ.ne_zero]
    rw [hs.tsum_eq_add_tsum_ite 0, h3, (algebraMap F (AdeleRing (𝓞 F) F)).map_zero, zero_add]
    exact add_comm _ _
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro p
    obtain ⟨u, hu, hub⟩ := hU {p} isCompact_singleton
    exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun ξ => hub ξ p rfl) hu
  · intro Z hZ
    obtain ⟨u, hu, hub⟩ := hU Z hZ
    exact tendstoUniformlyOn_tsum hu (fun ξ p hp => by rw [norm_norm]; exact hub ξ p hp)
  · refine continuous_iff_continuousAt.2 fun p0 => ?_
    obtain ⟨K, hK, hKn⟩ := exists_compact_mem_nhds p0
    obtain ⟨u, hu, hub⟩ := hU K hK
    exact (continuousOn_tsum (fun ξ => (hcont ξ).continuousOn) hu
      (fun ξ p hp => hub ξ p hp)).continuousAt hKn
  · intro g x η
    rw [hfull g (x + algebraMap F (AdeleRing (𝓞 F) F) η), hfull g x]
    have : ∀ ξ : F, algebraMap F (AdeleRing (𝓞 F) F) ξ +
        (x + algebraMap F (AdeleRing (𝓞 F) F) η) =
        algebraMap F (AdeleRing (𝓞 F) F) (ξ + η) + x := by
      intro ξ; rw [map_add]; abel
    simp_rw [this]
    exact (Equiv.addRight η).tsum_eq (fun ξ => f.eval ((g : AdeleRing (𝓞 F) F) *
      (algebraMap F (AdeleRing (𝓞 F) F) ξ + x)))
