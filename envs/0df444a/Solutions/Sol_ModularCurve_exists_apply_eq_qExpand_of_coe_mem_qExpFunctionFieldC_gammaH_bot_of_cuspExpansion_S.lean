-- Prove2me | solution 1 for ModularCurve.exists_apply_eq_qExpand_of_coe_mem_qExpFunctionFieldC_gammaH_bot_of_cuspExpansion_S
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/591bdcc1-0002-511a-9c64-10950c0083ba

import Mathlib
import Definitions.Def_ModularCurve_XH
import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_JqCoeff
import Theorems.Thm_ModularCurve_exists_isIntegral_level_pow_mul_qExpansion_slash_coeff
import Theorems.Thm_UpperHalfPlane_qExpansion_coeff_mul_width
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_apply_eq_qExpand_of_coe_mem_qExpFunctionFieldC_gammaH_bot_of_cuspExpansion_S
p2m_attr_erase "instance" "CohCarrier.HeckeData.V_isScalarTower CohCarrier.HeckeData.opSubalgebra_isMulCommutative CohCarrier.HeckeData.mTheta_isPrime"
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL CohCarrier.Gen.dia.sizeOf_spec CohCarrier.Gen.U.injEq CohCarrier.Gen.T.sizeOf_spec CohCarrier.Gen.U.sizeOf_spec CohCarrier.Gen.T.injEq CohCarrier.Gen.dia.injEq CohCarrier.HeckeData.mk.sizeOf_spec CohCarrier.HeckeData.opAlgHom_X CohCarrier.HeckeData.toMLₒ_apply CohCarrier.HeckeData.mk.injEq CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply"

set_option autoImplicit false

open scoped MatrixGroups ModularForm Manifold
open Complex UpperHalfPlane ModularForm CongruenceSubgroup Function

namespace NC1

theorem gamma1_le_gammaH_bot {N M : ℕ} [NeZero N] (h : N ∣ M) :
    CongruenceSubgroup.Gamma1 M ≤ CohCarrier.GammaH N ⊥ := by
  intro A hA
  rw [Gamma1_mem] at hA
  obtain ⟨h00, h11, h10⟩ := hA
  have cast_eq : ∀ x : ℤ, ZMod.castHom h (ZMod N) ((x : ZMod M)) = (x : ZMod N) := fun x => by simp
  have h11' : ((A 1 1 : ℤ) : ZMod N) = 1 := by rw [← cast_eq, h11, map_one]
  have h10' : ((A 1 0 : ℤ) : ZMod N) = 0 := by rw [← cast_eq, h10, map_zero]
  have hA0 : A ∈ Gamma0 N := Gamma0_mem.mpr h10'
  refine CohCarrier.mem_GammaH_iff.mpr ⟨hA0, ?_⟩
  rw [Subgroup.mem_bot]
  ext
  simp only [CohCarrier.val_gamma0Units, Units.val_one]
  exact h11'

section ConjT
variable {M p : ℕ}
theorem conj_T_pow_mem {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 M) :
    γ * ModularGroup.T ^ (p : ℤ) * γ⁻¹ ∈ Gamma1 (M * p) := by
  have hc : (M : ℤ) ∣ γ 1 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (Gamma0_mem.mp hγ)
  obtain ⟨r, hr⟩ := hc
  have hdet : (γ 0 0 : ℤ) * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    have := γ.det_coe; rwa [Matrix.det_fin_two] at this
  have h00 : (γ * ModularGroup.T ^ (p : ℤ) * γ⁻¹) 0 0 = 1 - γ 0 0 * γ 1 0 * p := by
    rw [Matrix.SpecialLinearGroup.SL2_inv_expl γ]
    simp only [Matrix.SpecialLinearGroup.coe_mul, ModularGroup.coe_T_zpow]
    simp [Matrix.mul_apply, Fin.sum_univ_two]
    linear_combination hdet
  have h11 : (γ * ModularGroup.T ^ (p : ℤ) * γ⁻¹) 1 1 = 1 + γ 0 0 * γ 1 0 * p := by
    rw [Matrix.SpecialLinearGroup.SL2_inv_expl γ]
    simp only [Matrix.SpecialLinearGroup.coe_mul, ModularGroup.coe_T_zpow]
    simp [Matrix.mul_apply, Fin.sum_univ_two]
    linear_combination hdet
  have h10 : (γ * ModularGroup.T ^ (p : ℤ) * γ⁻¹) 1 0 = -(γ 1 0 * γ 1 0 * p) := by
    rw [Matrix.SpecialLinearGroup.SL2_inv_expl γ]
    simp only [Matrix.SpecialLinearGroup.coe_mul, ModularGroup.coe_T_zpow]
    simp [Matrix.mul_apply, Fin.sum_univ_two]
    ring
  have hN0' : (M : ZMod (M * p)) * (p : ZMod (M * p)) = 0 := by
    exact_mod_cast ZMod.natCast_self (M * p)
  rw [Gamma1_mem, h00, h11, h10, hr]
  push_cast
  refine ⟨?_, ?_, ?_⟩
  · linear_combination (-(((γ 0 0 : ℤ) : ZMod (M * p)) * (r : ZMod (M * p)))) * hN0'
  · linear_combination (((γ 0 0 : ℤ) : ZMod (M * p)) * (r : ZMod (M * p))) * hN0'
  · linear_combination (-((M : ZMod (M * p)) * (r : ZMod (M * p)) * (r : ZMod (M * p)))) * hN0'
end ConjT

theorem S_mul_T_zpow_mul_S_inv_mem (N : ℕ) :
    ModularGroup.S * ModularGroup.T ^ (N : ℤ) * ModularGroup.S⁻¹ ∈ CongruenceSubgroup.Gamma1 N := by
  have hS : ModularGroup.S ∈ Gamma0 1 := by
    rw [Gamma0_mem]; exact Subsingleton.elim _ _
  have := conj_T_pow_mem (M := 1) (p := N) hS
  rwa [one_mul] at this

theorem periodic_of_T_zpow_invariant {G : ℍ → ℂ} (n : ℕ)
    (h : ∀ τ : ℍ, G ((ModularGroup.T ^ (n : ℤ)) • τ) = G τ) : Periodic (G ∘ ofComplex) n := by
  intro w
  by_cases hw : 0 < im w
  · have this : 0 < im (w + n) := by simp [hw]
    simp only [comp_apply, ofComplex_apply_of_im_pos this, ofComplex_apply_of_im_pos hw]
    have := h ⟨w, hw⟩
    rw [modular_T_zpow_smul] at this
    convert this using 2
    ext
    simp [add_comm, UpperHalfPlane.coe_vadd]
  · push Not at hw
    have : im (w + n) ≤ 0 := by simpa using hw
    simp [ofComplex_apply_of_im_nonpos this, ofComplex_apply_of_im_nonpos hw]

theorem periodic_slash_S {N : ℕ} [NeZero N] {k : ℤ}
    (f : ModularForm (CohCarrier.GammaH N ⊥ : Subgroup (GL (Fin 2) ℝ)) k) :
    Periodic (((⇑f : ℍ → ℂ) ∣[k] ModularGroup.S) ∘ ofComplex) (N : ℝ) := by
  apply periodic_of_T_zpow_invariant
  intro τ
  have hmem : ModularGroup.S * ModularGroup.T ^ (N : ℤ) * ModularGroup.S⁻¹ ∈ CohCarrier.GammaH N ⊥ :=
    gamma1_le_gammaH_bot (dvd_refl N) (S_mul_T_zpow_mul_S_inv_mem N)
  have hinv : (⇑f : ℍ → ℂ) ∣[k] (ModularGroup.S * ModularGroup.T ^ (N : ℤ) * ModularGroup.S⁻¹) = ⇑f := by
    rw [SL_slash]
    exact SlashInvariantForm.slash_action_eqn f _ (Subgroup.mem_map_of_mem _ hmem)
  have key : ((⇑f : ℍ → ℂ) ∣[k] ModularGroup.S) ∣[k] (ModularGroup.T ^ (N : ℤ)) = (⇑f : ℍ → ℂ) ∣[k] ModularGroup.S := by
    rw [← SlashAction.slash_mul]
    conv_lhs => rw [show ModularGroup.S * ModularGroup.T ^ (N : ℤ) =
      (ModularGroup.S * ModularGroup.T ^ (N : ℤ) * ModularGroup.S⁻¹) * ModularGroup.S by group]
    rw [SlashAction.slash_mul, hinv]
  have := congrFun key τ
  rw [SL_slash_apply] at this
  have hden : denom (↑(ModularGroup.T ^ (N : ℤ)) : GL (Fin 2) ℝ) τ = 1 := by
    rw [ModularGroup.denom_apply, ModularGroup.coe_T_zpow]; simp
  rw [hden, one_zpow, mul_one] at this
  exact this

theorem exists_ofPowerSeries_eq_qExpand (K : Type*) [Field K] (d : ℕ) [NeZero d]
    (P : PowerSeries K) (hP : ∀ n : ℕ, ¬ d ∣ n → PowerSeries.coeff n P = 0) :
    ∃ y : LaurentSeries K, HahnSeries.ofPowerSeries ℤ K P = ModularCurve.qExpand K d y := by
  refine ⟨HahnSeries.ofPowerSeries ℤ K (PowerSeries.mk fun m => PowerSeries.coeff (d * m) P), ?_⟩
  have hd0 : (0 : ℤ) < d := by exact_mod_cast NeZero.pos d
  ext i
  rcases lt_or_ge i 0 with hi | hi
  · rw [ModularCurve.ofPowerSeries_coeff_of_neg _ hi]
    by_cases hdi : (d : ℤ) ∣ i
    · obtain ⟨m, rfl⟩ := hdi
      have hm : m < 0 := by
        by_contra hm; push_neg at hm; exact absurd hi (not_lt.mpr (mul_nonneg hd0.le hm))
      rw [ModularCurve.qExpand_coeff_mul, ModularCurve.ofPowerSeries_coeff_of_neg _ hm]
    · rw [ModularCurve.qExpand_coeff_of_not_dvd _ _ hdi]
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hi
    rw [HahnSeries.ofPowerSeries_apply_coeff]
    by_cases hdn : d ∣ n
    · obtain ⟨m, rfl⟩ := hdn
      rw [show ((d * m : ℕ) : ℤ) = (d : ℤ) * (m : ℤ) by push_cast; ring, ModularCurve.qExpand_coeff_mul,
        HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_mk]
    · rw [hP n hdn, ModularCurve.qExpand_coeff_of_not_dvd]
      exact fun h => hdn (Int.natCast_dvd_natCast.mp h)

end NC1

theorem solution
    (M : ℕ) [NeZero M] {ℓ : ℕ} [Fact ℓ.Prime] (hℓM : ¬ ℓ ∣ M)
    (K : Type*) [Field K] [IsAlgClosed K] [CharP K ℓ]
    (φ : integralClosure ℤ ℂ →+* K)
    (N d : ℕ) [NeZero N] [NeZero d] (hM : N * d = M)
    (Θ : ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH M ⊥) →ₐ[K] LaurentSeries K)
    (hΘ :
      ∀ (k : ℤ) (f h : ModularForm (CohCarrier.GammaH M ⊥ : Subgroup (GL (Fin 2) ℝ)) k)
        (pf ph : PowerSeries ℤ), ModularCurve.IsIntegralQExp f pf →
        ModularCurve.IsIntegralQExp h ph → ModularCurve.intSeriesC K ph ≠ 0 →
        ∀ (a : ℕ) (F G : PowerSeries (integralClosure ℤ ℂ)),
          F.map (algebraMap (integralClosure ℤ ℂ) ℂ) =
            (M : ℂ) ^ a • UpperHalfPlane.qExpansion M ((⇑f : UpperHalfPlane → ℂ) ∣[k] ModularGroup.S) →
          G.map (algebraMap (integralClosure ℤ ℂ) ℂ) =
            (M : ℂ) ^ a • UpperHalfPlane.qExpansion M ((⇑h : UpperHalfPlane → ℂ) ∣[k] ModularGroup.S) →
          ∀ x : ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH M ⊥),
            (x : LaurentSeries K) = ModularCurve.intSeriesC K pf / ModularCurve.intSeriesC K ph →
            HahnSeries.ofPowerSeries ℤ K (G.map φ) ≠ 0 ∧
              (Θ x : LaurentSeries K) =
                HahnSeries.ofPowerSeries ℤ K (F.map φ) / HahnSeries.ofPowerSeries ℤ K (G.map φ)) :
    ∀ x : ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH M ⊥),
      (x : LaurentSeries K) ∈ ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH N ⊥) →
        ∃ y : LaurentSeries K, (Θ x : LaurentSeries K) = ModularCurve.qExpand K d y := by
  classical
  have hNM : N ∣ M := ⟨d, hM.symm⟩

  have hMN_SL : CohCarrier.GammaH M ⊥ ≤ CohCarrier.GammaH N ⊥ := fun A hA =>
    NC1.gamma1_le_gammaH_bot hNM (by
      obtain ⟨hA0, hH⟩ := CohCarrier.mem_GammaH_iff.mp hA
      rw [Subgroup.mem_bot] at hH
      have hd : ((A 1 1 : ℤ) : ZMod M) = 1 := by
        have := congrArg (fun u : (ZMod M)ˣ => (u : ZMod M)) hH
        first
          | simpa [CohCarrier.val_gamma0Units] using this
          | simpa [CohCarrier.val_gamma0Units, Gamma0Map] using this
          | (simp [CohCarrier.val_gamma0Units] at this; exact this)
      have hc : ((A 1 0 : ℤ) : ZMod M) = 0 := Gamma0_mem.mp hA0
      have hdet : (A 0 0 : ℤ) * A 1 1 - A 0 1 * A 1 0 = 1 := by
        have := A.det_coe; rwa [Matrix.det_fin_two] at this
      have ha : ((A 0 0 : ℤ) : ZMod M) = 1 := by
        have := congrArg (fun z : ℤ => (z : ZMod M)) hdet
        push_cast at this
        rw [hd, hc, mul_one, mul_zero, sub_zero] at this
        exact this
      exact (Gamma1_mem _ _).mpr ⟨ha, hd, hc⟩)
  have hMN : (CohCarrier.GammaH M ⊥ : Subgroup (GL (Fin 2) ℝ)) ≤ (CohCarrier.GammaH N ⊥ : Subgroup (GL (Fin 2) ℝ)) :=
    Subgroup.map_mono hMN_SL
  have h1N : (CongruenceSubgroup.Gamma1 M : Subgroup (GL (Fin 2) ℝ)) ≤ (CohCarrier.GammaH N ⊥ : Subgroup (GL (Fin 2) ℝ)) :=
    Subgroup.map_mono (NC1.gamma1_le_gammaH_bot hNM)
  have hsub : ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH N ⊥) ≤ ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH M ⊥) :=
    ModularCurve.qExpFunctionFieldC_mono K hMN_SL
  suffices H : ∀ (s : LaurentSeries K) (hs : s ∈ ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH N ⊥)),
      ∃ y : LaurentSeries K, (Θ ⟨s, hsub hs⟩ : LaurentSeries K) = ModularCurve.qExpand K d y by
    intro x hx
    obtain ⟨y, hy⟩ := H x hx
    exact ⟨y, by simpa using hy⟩
  intro s hs
  induction hs using IntermediateField.adjoin_induction with
  | mem s hs =>
    obtain ⟨k, f, g, pf, pg, hf, hg, hg0, rfl⟩ := hs
    obtain ⟨af, haf⟩ := ModularCurve.exists_isIntegral_level_pow_mul_qExpansion_slash_coeff M
      (ModularCurve.restrictForm h1N f) hf ModularGroup.S
    obtain ⟨ag, hag⟩ := ModularCurve.exists_isIntegral_level_pow_mul_qExpansion_slash_coeff M
      (ModularCurve.restrictForm h1N g) hg ModularGroup.S
    have hMint : ∀ b : ℕ, IsIntegral ℤ ((M : ℂ) ^ b) := fun b => by
      simpa using (isIntegral_algebraMap (R := ℤ) (A := ℂ) (x := (M : ℤ) ^ b))
    have hFint : ∀ n : ℕ, IsIntegral ℤ ((M : ℂ) ^ (af + ag) *
        PowerSeries.coeff n (UpperHalfPlane.qExpansion M ((⇑f : ℍ → ℂ) ∣[k] ModularGroup.S))) := fun n => by
      rw [pow_add, mul_comm ((M : ℂ) ^ af), mul_assoc]
      exact (hMint ag).mul (haf n)
    have hGint : ∀ n : ℕ, IsIntegral ℤ ((M : ℂ) ^ (af + ag) *
        PowerSeries.coeff n (UpperHalfPlane.qExpansion M ((⇑g : ℍ → ℂ) ∣[k] ModularGroup.S))) := fun n => by
      rw [pow_add, mul_assoc]
      exact (hMint af).mul (hag n)
    let F : PowerSeries (integralClosure ℤ ℂ) := PowerSeries.mk fun n => ⟨_, hFint n⟩
    let G : PowerSeries (integralClosure ℤ ℂ) := PowerSeries.mk fun n => ⟨_, hGint n⟩
    have hF : F.map (algebraMap (integralClosure ℤ ℂ) ℂ) =
        (M : ℂ) ^ (af + ag) • UpperHalfPlane.qExpansion M ((⇑f : ℍ → ℂ) ∣[k] ModularGroup.S) := by
      ext n; simp [F, PowerSeries.coeff_map, PowerSeries.coeff_mk]
    have hG : G.map (algebraMap (integralClosure ℤ ℂ) ℂ) =
        (M : ℂ) ^ (af + ag) • UpperHalfPlane.qExpansion M ((⇑g : ℍ → ℂ) ∣[k] ModularGroup.S) := by
      ext n; simp [G, PowerSeries.coeff_map, PowerSeries.coeff_mk]
    obtain ⟨hG0, hΘx⟩ := hΘ k (ModularCurve.restrictForm hMN f) (ModularCurve.restrictForm hMN g) pf pg hf hg hg0
      (af + ag) F G hF hG ⟨_, hsub (ModularCurve.div_mem_qExpFunctionFieldC f g hf hg hg0)⟩ rfl
    have hMreal : ((d : ℕ) : ℝ) * (N : ℝ) = (M : ℝ) := by exact_mod_cast (by rw [mul_comm]; exact hM : d * N = M)
    have hsupp : ∀ (u : ModularForm (CohCarrier.GammaH N ⊥ : Subgroup (GL (Fin 2) ℝ)) k) (n : ℕ), ¬ d ∣ n →
        PowerSeries.coeff n (UpperHalfPlane.qExpansion M ((⇑u : ℍ → ℂ) ∣[k] ModularGroup.S)) = 0 := by
      intro u n hn
      have hhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) ((⇑u : ℍ → ℂ) ∣[k] ModularGroup.S) := by
        rw [SL_slash]; exact u.holo'.slash _ _
      have hbdd : IsBoundedAtImInfty ((⇑u : ℍ → ℂ) ∣[k] ModularGroup.S) := by
        have := ModularFormClass.bdd_at_infty_slash (ModularCurve.restrictForm h1N u) ModularGroup.S
        simpa using this
      have := UpperHalfPlane.qExpansion_coeff_mul_width ((⇑u : ℍ → ℂ) ∣[k] ModularGroup.S) N
        (by exact_mod_cast NeZero.pos N) (NC1.periodic_slash_S u) hhol hbdd d (NeZero.pos d) n
      rw [hMreal] at this
      rw [this, if_neg hn]
    have hFφ : ∀ n : ℕ, ¬ d ∣ n → PowerSeries.coeff n (F.map φ) = 0 := fun n hn => by
      simp [F, PowerSeries.coeff_map, PowerSeries.coeff_mk, hsupp f n hn]
    have hGφ : ∀ n : ℕ, ¬ d ∣ n → PowerSeries.coeff n (G.map φ) = 0 := fun n hn => by
      simp [G, PowerSeries.coeff_map, PowerSeries.coeff_mk, hsupp g n hn]
    obtain ⟨yF, hyF⟩ := NC1.exists_ofPowerSeries_eq_qExpand K d (F.map φ) hFφ
    obtain ⟨yG, hyG⟩ := NC1.exists_ofPowerSeries_eq_qExpand K d (G.map φ) hGφ
    refine ⟨yF / yG, ?_⟩
    rw [map_div₀, ← hyF, ← hyG, ← hΘx]
  | algebraMap c =>
    refine ⟨HahnSeries.C c, ?_⟩
    rw [ModularCurve.qExpand_C]
    have : (⟨algebraMap K (LaurentSeries K) c, hsub (IntermediateField.algebraMap_mem _ c)⟩ :
        ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH M ⊥)) = algebraMap K _ c := rfl
    rw [this, AlgHom.commutes]
    show HahnSeries.ofPowerSeries ℤ K (algebraMap K (PowerSeries K) c) = _
    rw [PowerSeries.algebraMap_eq]; exact HahnSeries.ofPowerSeries_C c
  | add s t hs ht ihs iht =>
    obtain ⟨y₁, hy₁⟩ := ihs; obtain ⟨y₂, hy₂⟩ := iht
    refine ⟨y₁ + y₂, ?_⟩
    have : (⟨s + t, hsub (add_mem hs ht)⟩ : ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH M ⊥)) =
        ⟨s, hsub hs⟩ + ⟨t, hsub ht⟩ := rfl
    have hadd : Θ (⟨s, hsub hs⟩ + ⟨t, hsub ht⟩) = Θ ⟨s, hsub hs⟩ + Θ ⟨t, hsub ht⟩ := Θ.toRingHom.map_add _ _
    rw [this, hadd, (ModularCurve.qExpand K d).map_add, hy₁, hy₂]
  | mul s t hs ht ihs iht =>
    obtain ⟨y₁, hy₁⟩ := ihs; obtain ⟨y₂, hy₂⟩ := iht
    refine ⟨y₁ * y₂, ?_⟩
    have : (⟨s * t, hsub (mul_mem hs ht)⟩ : ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH M ⊥)) =
        ⟨s, hsub hs⟩ * ⟨t, hsub ht⟩ := rfl
    have hmul : Θ (⟨s, hsub hs⟩ * ⟨t, hsub ht⟩) = Θ ⟨s, hsub hs⟩ * Θ ⟨t, hsub ht⟩ := Θ.toRingHom.map_mul _ _
    rw [this, hmul, (ModularCurve.qExpand K d).map_mul, hy₁, hy₂]
  | inv s hs ihs =>
    obtain ⟨y₁, hy₁⟩ := ihs
    refine ⟨y₁⁻¹, ?_⟩
    have : (⟨s⁻¹, hsub (inv_mem hs)⟩ : ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH M ⊥)) =
        (⟨s, hsub hs⟩)⁻¹ := rfl
    have hinv : Θ ((⟨s, hsub hs⟩)⁻¹) = (Θ ⟨s, hsub hs⟩)⁻¹ := map_inv₀ Θ.toRingHom _
    rw [this, hinv, map_inv₀ (ModularCurve.qExpand K d), hy₁]

end S_ModularCurve_exists_apply_eq_qExpand_of_coe_mem_qExpFunctionFieldC_gammaH_bot_of_cuspExpansion_S
end P2MW
export P2MW.S_ModularCurve_exists_apply_eq_qExpand_of_coe_mem_qExpFunctionFieldC_gammaH_bot_of_cuspExpansion_S (solution)
