-- Prove2me | solution 1 for ModularCurve.diamondAutHBar_eq_refl_of_mem_or_neg_mem
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/0f7273de-d24f-5521-b068-6a877e6c7a2d

import Mathlib
import Definitions.Def_ModularCurve_XHOperators
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_diamondAutHBar_eq_refl_of_mem_or_neg_mem

set_option autoImplicit false

noncomputable section

open scoped MatrixGroups ModularForm

namespace DiamondTrivialSol

open UpperHalfPlane CongruenceSubgroup ModularCurve IntermediateField HahnSeries

local notation "Qb" => AlgebraicClosure ℚ

variable {M : ℕ} [NeZero M] {H : Subgroup (ZMod M)ˣ}

abbrev Γ (M : ℕ) (H : Subgroup (ZMod M)ˣ) : Subgroup (GL (Fin 2) ℝ) :=
  ((CohCarrier.GammaH M H : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

omit [NeZero M] in
theorem one_mem_strictPeriods : (1 : ℝ) ∈ (Γ M H).strictPeriods := by
  rw [Subgroup.strictPeriods_eq_zmultiples_one_of_T_mem (translation_mem_GammaH M H)]
  exact AddSubgroup.mem_zmultiples _

omit [NeZero M] in
theorem coeGL_neg (A : SL(2, ℤ)) : ((-A : SL(2, ℤ)) : GL (Fin 2) ℝ) = -(A : GL (Fin 2) ℝ) := by
  ext i j
  simp

omit [NeZero M] in

theorem slash_neg (k : ℤ) (f : ℍ → ℂ) (A : SL(2, ℤ)) :
    f ∣[k] (-A) = ((-1 : ℂ) ^ k) • (f ∣[k] A) := by
  funext τ
  rw [ModularForm.SL_slash_apply, Pi.smul_apply, ModularForm.SL_slash_apply, smul_eq_mul,
    ModularGroup.SL_neg_smul]
  rw [coeGL_neg, denom_neg, neg_eq_neg_one_mul, mul_zpow, ← mul_assoc, mul_comm (f _), mul_assoc]
  congr 1
  rw [zpow_neg, ← inv_zpow, inv_neg, inv_one]

omit [NeZero M] in
theorem slash_of_mem {k : ℤ} (f : ModularForm (Γ M H) k) {γ : SL(2, ℤ)}
    (hγ : γ ∈ CohCarrier.GammaH M H) : (⇑f : ℍ → ℂ) ∣[k] γ = ⇑f := by
  rw [ModularForm.SL_slash]
  exact SlashInvariantForm.slash_action_eqn f _
    (Subgroup.mem_map_of_mem (Matrix.SpecialLinearGroup.mapGL ℝ) hγ)

theorem exists_gamma (d : (ZMod M)ˣ) (hd : d ∈ H ∨ -d ∈ H) (k : ℤ) :
    ∃ γ : SL(2, ℤ), γ ∈ Gamma0 M ∧ ((γ 0 0 : ℤ) : ZMod M) = (d : ZMod M) ∧
      ∃ c : ℂ, c ≠ 0 ∧ ∀ f : ModularForm (Γ M H) k, (⇑f : ℍ → ℂ) ∣[k] γ = c • ⇑f := by
  obtain ⟨γ₀, hγ₀⟩ := CohCarrier.gamma0Units_surjective M d⁻¹
  have h00 : ((γ₀.1 0 0 : ℤ) : ZMod M) = (d : ZMod M) := by
    have h : (((CohCarrier.gamma0Units M γ₀)⁻¹ : (ZMod M)ˣ) : ZMod M) = ((γ₀.1 0 0 : ℤ) : ZMod M) := rfl
    rw [← h, hγ₀, inv_inv]
  refine ⟨γ₀.1, γ₀.2, h00, ?_⟩
  rcases hd with hd | hd
  ·
    have hmem : (γ₀.1 : SL(2, ℤ)) ∈ CohCarrier.GammaH M H :=
      CohCarrier.mem_GammaH_iff.mpr ⟨γ₀.2, by rw [hγ₀]; exact inv_mem hd⟩
    exact ⟨1, one_ne_zero, fun f => by rw [slash_of_mem f hmem, one_smul]⟩
  ·
    have hneg0 : (-γ₀.1 : SL(2, ℤ)) ∈ Gamma0 M := by
      have h := Gamma0_mem.mp γ₀.2
      rw [Gamma0_mem]
      simp only [Matrix.SpecialLinearGroup.coe_neg, Matrix.neg_apply, Int.cast_neg, h, neg_zero]
    have hunits : CohCarrier.gamma0Units M ⟨-γ₀.1, hneg0⟩ = -(CohCarrier.gamma0Units M γ₀) := by
      ext
      simp [CohCarrier.gamma0Units, Gamma0Map]
    have hmem : (-γ₀.1 : SL(2, ℤ)) ∈ CohCarrier.GammaH M H := by
      refine CohCarrier.mem_GammaH_iff.mpr ⟨hneg0, ?_⟩
      rw [hunits, hγ₀]
      have e : (-d)⁻¹ = -d⁻¹ := Units.ext rfl
      rw [← e]
      exact inv_mem hd
    refine ⟨(-1 : ℂ) ^ k, zpow_ne_zero k (by norm_num), fun f => ?_⟩
    have h1 : (⇑f : ℍ → ℂ) ∣[k] (-γ₀.1) = ⇑f := slash_of_mem f hmem
    have h2 := slash_neg k (⇑f) (-γ₀.1)
    rw [neg_neg, h1] at h2
    exact h2

def qC (F : ℍ → ℂ) : LaurentSeries ℂ := ofPowerSeries ℤ ℂ (qExpansion 1 F)

omit [NeZero M] in
theorem qC_smul {k : ℤ} (c : ℂ) (f : ModularForm (Γ M H) k) :
    qC (c • ⇑f) = HahnSeries.C c * qC f := by
  rw [qC, qC, ModularForm.qExpansion_smul one_pos one_mem_strictPeriods c f,
    ← HahnSeries.ofPowerSeries_C, ← map_mul, PowerSeries.smul_eq_C_mul]

abbrev ιC : LaurentSeries ℚ →+* LaurentSeries ℂ := coeffMap (algebraMap ℚ ℂ)

omit [NeZero M] in
theorem ιC_intSeriesC {F : ℍ → ℂ} {p : PowerSeries ℤ} (h : IsIntegralQExp F p) :
    ιC (intSeriesC ℚ p) = qC F := by
  rw [qC, ← h]
  ext n
  simp only [intSeriesC, coeffMap_coeff, PowerSeries.coeff_coe]
  split_ifs
  · exact map_zero _
  · simp [PowerSeries.coeff_map]

theorem sigma_generator {d : (ZMod M)ˣ} (hd : d ∈ H ∨ -d ∈ H)
    {σ : xHFunctionFieldBar M H ≃ₐ[Qb] xHFunctionFieldBar M H} (hσ : IsDiamondAutHBar M H d σ)
    {k : ℤ} (f g : ModularForm (Γ M H) k) {pf pg : PowerSeries ℤ}
    (hf : IsIntegralQExp f pf) (hg : IsIntegralQExp g pg) (hg0 : intSeriesC ℚ pg ≠ 0) :
    ((σ ⟨coeffEmb Qb (intSeriesC ℚ pf / intSeriesC ℚ pg),
        coeffEmb_mem_laurentBaseChange Qb (div_mem_qExpFunctionFieldC f g hf hg hg0)⟩ :
        xHFunctionFieldBar M H) : LaurentSeries Qb) =
      coeffEmb Qb (intSeriesC ℚ pf / intSeriesC ℚ pg) := by
  obtain ⟨γ, hγ0, hγd, c, hc, hslash⟩ := exists_gamma (M := M) (H := H) d hd k
  obtain ⟨y, -, hσy, hy⟩ := hσ k f g pf pg hf hg hg0 γ hγ0 hγd
  rw [hσy]
  congr 1

  rw [← ModularForm.SL_slash, ← ModularForm.SL_slash, hslash f, hslash g] at hy
  change ιC y * qC (c • ⇑g) = qC (c • ⇑f) at hy
  rw [qC_smul, qC_smul, mul_left_comm] at hy
  have hy' : ιC y * qC g = qC f :=
    mul_left_cancel₀ ((map_ne_zero_iff _ HahnSeries.C_injective).mpr hc) hy
  have hgC : qC g ≠ 0 := by
    rw [← ιC_intSeriesC hg]
    exact (map_ne_zero_iff _ (RingHom.injective _)).mpr hg0
  apply (RingHom.injective ιC)
  rw [map_div₀, ιC_intSeriesC hf, ιC_intSeriesC hg, eq_div_iff hgC]
  exact hy'

omit [NeZero M] in
theorem coeffEmb_algebraMap (c : ℚ) :
    coeffEmb Qb (algebraMap ℚ (LaurentSeries ℚ) c) = algebraMap Qb (LaurentSeries Qb) (algebraMap ℚ Qb c) := by
  rw [ModularCurve.algebraMap_laurentSeries_eq_single, ModularCurve.algebraMap_laurentSeries_eq_single,
    coeffEmb, coeffMap_single]

theorem eq_refl_of_isDiamondAutHBar {d : (ZMod M)ˣ} (hd : d ∈ H ∨ -d ∈ H)
    {σ : xHFunctionFieldBar M H ≃ₐ[Qb] xHFunctionFieldBar M H} (hσ : IsDiamondAutHBar M H d σ) :
    σ = AlgEquiv.refl := by

  suffices key : ∀ (x : LaurentSeries Qb) (hx : x ∈ xHFunctionFieldBar M H),
      ((σ ⟨x, hx⟩ : xHFunctionFieldBar M H) : LaurentSeries Qb) = x by
    exact AlgEquiv.ext fun x => Subtype.ext (key x.1 x.2)

  intro x hx
  induction hx using IntermediateField.adjoin_induction with
  | mem s hs =>
      obtain ⟨z, hz, rfl⟩ := hs

      change z ∈ qExpFunctionFieldC ℚ (CohCarrier.GammaH M H) at hz
      induction hz using IntermediateField.adjoin_induction with
      | mem r hr =>
          obtain ⟨k, f, g, pf, pg, hf, hg, hg0, rfl⟩ := hr
          exact sigma_generator hd hσ f g hf hg hg0
      | algebraMap c =>
          have hmem : coeffEmb Qb (algebraMap ℚ (LaurentSeries ℚ) c) ∈ xHFunctionFieldBar M H :=
            coeffEmb_mem_laurentBaseChange Qb (IntermediateField.algebraMap_mem _ c)
          have : (⟨coeffEmb Qb (algebraMap ℚ (LaurentSeries ℚ) c), hmem⟩ : xHFunctionFieldBar M H) =
              algebraMap Qb (xHFunctionFieldBar M H) (algebraMap ℚ Qb c) :=
            Subtype.ext (coeffEmb_algebraMap c)
          rw [this, AlgEquiv.commutes, coeffEmb_algebraMap]
          rfl
      | add y z hy hz ihy ihz =>
          have hy' : coeffEmb Qb y ∈ xHFunctionFieldBar M H := coeffEmb_mem_laurentBaseChange Qb hy
          have hz' : coeffEmb Qb z ∈ xHFunctionFieldBar M H := coeffEmb_mem_laurentBaseChange Qb hz
          have : (⟨coeffEmb Qb (y + z), coeffEmb_mem_laurentBaseChange Qb (add_mem hy hz)⟩ :
              xHFunctionFieldBar M H) = ⟨coeffEmb Qb y, hy'⟩ + ⟨coeffEmb Qb z, hz'⟩ :=
            Subtype.ext (map_add _ _ _)
          rw [this, map_add σ, map_add (coeffEmb Qb)]
          change ((σ ⟨coeffEmb Qb y, hy'⟩ : xHFunctionFieldBar M H) : LaurentSeries Qb) +
              ((σ ⟨coeffEmb Qb z, hz'⟩ : xHFunctionFieldBar M H) : LaurentSeries Qb) = _
          rw [ihy, ihz]
      | inv y hy ihy =>
          have hy' : coeffEmb Qb y ∈ xHFunctionFieldBar M H := coeffEmb_mem_laurentBaseChange Qb hy
          have : (⟨coeffEmb Qb y⁻¹, coeffEmb_mem_laurentBaseChange Qb (inv_mem hy)⟩ :
              xHFunctionFieldBar M H) = ⟨coeffEmb Qb y, hy'⟩⁻¹ :=
            Subtype.ext (map_inv₀ _ _)
          rw [this, map_inv₀ σ, map_inv₀ (coeffEmb Qb)]
          change (((σ ⟨coeffEmb Qb y, hy'⟩ : xHFunctionFieldBar M H) : LaurentSeries Qb))⁻¹ = _
          rw [ihy]
      | mul y z hy hz ihy ihz =>
          have hy' : coeffEmb Qb y ∈ xHFunctionFieldBar M H := coeffEmb_mem_laurentBaseChange Qb hy
          have hz' : coeffEmb Qb z ∈ xHFunctionFieldBar M H := coeffEmb_mem_laurentBaseChange Qb hz
          have : (⟨coeffEmb Qb (y * z), coeffEmb_mem_laurentBaseChange Qb (mul_mem hy hz)⟩ :
              xHFunctionFieldBar M H) = ⟨coeffEmb Qb y, hy'⟩ * ⟨coeffEmb Qb z, hz'⟩ :=
            Subtype.ext (map_mul _ _ _)
          rw [this, map_mul σ, map_mul (coeffEmb Qb)]
          change ((σ ⟨coeffEmb Qb y, hy'⟩ : xHFunctionFieldBar M H) : LaurentSeries Qb) *
              ((σ ⟨coeffEmb Qb z, hz'⟩ : xHFunctionFieldBar M H) : LaurentSeries Qb) = _
          rw [ihy, ihz]
  | algebraMap c =>
      have : (⟨algebraMap Qb (LaurentSeries Qb) c, IntermediateField.algebraMap_mem _ c⟩ :
          xHFunctionFieldBar M H) = algebraMap Qb (xHFunctionFieldBar M H) c := rfl
      rw [this, AlgEquiv.commutes]
      rfl
  | add y z hy hz ihy ihz =>
      have : (⟨y + z, add_mem hy hz⟩ : xHFunctionFieldBar M H) = ⟨y, hy⟩ + ⟨z, hz⟩ := rfl
      rw [this, map_add]
      change ((σ ⟨y, hy⟩ : xHFunctionFieldBar M H) : LaurentSeries Qb) +
          ((σ ⟨z, hz⟩ : xHFunctionFieldBar M H) : LaurentSeries Qb) = _
      rw [ihy, ihz]
  | inv y hy ihy =>
      have : (⟨y⁻¹, inv_mem hy⟩ : xHFunctionFieldBar M H) = ⟨y, hy⟩⁻¹ := rfl
      rw [this, map_inv₀]
      change (((σ ⟨y, hy⟩ : xHFunctionFieldBar M H) : LaurentSeries Qb))⁻¹ = _
      rw [ihy]
  | mul y z hy hz ihy ihz =>
      have : (⟨y * z, mul_mem hy hz⟩ : xHFunctionFieldBar M H) = ⟨y, hy⟩ * ⟨z, hz⟩ := rfl
      rw [this, map_mul]
      change ((σ ⟨y, hy⟩ : xHFunctionFieldBar M H) : LaurentSeries Qb) *
          ((σ ⟨z, hz⟩ : xHFunctionFieldBar M H) : LaurentSeries Qb) = _
      rw [ihy, ihz]

end DiamondTrivialSol

end

open DiamondTrivialSol ModularCurve in
theorem solution (M : ℕ) [NeZero M]
    (H : Subgroup (ZMod M)ˣ) (d : (ZMod M)ˣ) (hd : d ∈ H ∨ -d ∈ H) :
    ModularCurve.diamondAutHBar M H d = AlgEquiv.refl := by
  rcases Classical.em (∃ σ : xHFunctionFieldBar M H ≃ₐ[AlgebraicClosure ℚ] xHFunctionFieldBar M H,
      IsDiamondAutHBar M H d σ) with h | h
  · exact eq_refl_of_isDiamondAutHBar hd (isDiamondAutHBar_diamondAutHBar h)
  · exact diamondAutHBar_of_not h

end S_ModularCurve_diamondAutHBar_eq_refl_of_mem_or_neg_mem
end P2MW
export P2MW.S_ModularCurve_diamondAutHBar_eq_refl_of_mem_or_neg_mem (solution)
