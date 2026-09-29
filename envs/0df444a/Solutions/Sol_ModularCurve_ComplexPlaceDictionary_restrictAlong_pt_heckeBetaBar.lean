-- Prove2me | solution 1 for ModularCurve.ComplexPlaceDictionary.restrictAlong_pt_heckeBetaBar
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/85ea3deb-0a23-5621-84b8-d6f1c2ddc00e

import Mathlib
import Definitions.Def_ModularCurve_ComplexPlaceDictionary
import Definitions.Def_ModularCurve_HeckeOperator
import Definitions.Def_ModularForm_HeckeOperator
import Theorems.Thm_ModularCurve_exists_modularForm_mul_qExpansion_eq_of_mem_laurentBaseChange
import Theorems.Thm_ModularCurve_realize_eq_div
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_ComplexPlaceDictionary_restrictAlong_pt_heckeBetaBar
p2m_attr_erase "simp" "ModularCurve.jqNModC_one"

set_option autoImplicit false

noncomputable section

p2m_open "UpperHalfPlane ModularForm ConjAct Filter ModularCurve P2MW.S_ModularCurve_ComplexPlaceDictionary_restrictAlong_pt_heckeBetaBar.ModularCurve AlgebraicCurve"
open scoped MatrixGroups ConjAct Pointwise Topology Manifold

namespace ModularCurve
p2m_export "ModularCurve" "realize ComplexPlaceDictionary qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd modularFunctionFieldFull laurentBaseChange heckeBetaBar coe_heckeBetaBar HeckeBetaBarIntegral exists_modularForm_mul_qExpansion_eq_of_mem_laurentBaseChange realize_eq_div"
namespace RestrictAlongPtHeckeBetaBar
p2m_open "ModularCurve"

def restrict {Γ Γ' : Subgroup (GL (Fin 2) ℝ)} (hle : Γ' ≤ Γ) {k : ℤ} (f : ModularForm Γ k)
    [Γ'.HasDetPlusMinusOne] : ModularForm Γ' k where
  toSlashInvariantForm := ⟨f, fun γ hγ => SlashInvariantForm.slash_action_eqn f γ (hle hγ)⟩
  holo' := f.holo'
  bdd_at_cusps' := fun hc => f.bdd_at_cusps' (hc.mono hle)

@[scoped simp] theorem coe_restrict {Γ Γ' : Subgroup (GL (Fin 2) ℝ)} (hle : Γ' ≤ Γ) {k : ℤ}
    (f : ModularForm Γ k) [Γ'.HasDetPlusMinusOne] :
    ((restrict hle f : ModularForm Γ' k) : ℍ → ℂ) = f := rfl

variable (N ℓ : ℕ)

def lowerConj (γ : SL(2, ℤ)) (hγ : (ℓ : ℤ) ∣ γ 1 0) : SL(2, ℤ) :=
  ⟨!![γ 0 0, ℓ * γ 0 1; γ 1 0 / ℓ, γ 1 1], by
    have hdet := Matrix.det_fin_two γ.1
    rw [γ.2] at hdet
    have hdiv : (ℓ : ℤ) * (γ 1 0 / ℓ) = γ 1 0 := Int.mul_ediv_cancel' hγ
    rw [Matrix.det_fin_two_of]
    have : (γ 0 0 * γ 1 1 - ↑ℓ * γ 0 1 * (γ 1 0 / ↑ℓ) : ℤ) =
        γ 0 0 * γ 1 1 - γ 0 1 * (↑ℓ * (γ 1 0 / ↑ℓ)) := by ring
    rw [this, hdiv]
    linarith⟩

theorem lowerConj_apply_one_zero (γ : SL(2, ℤ)) (hγ : (ℓ : ℤ) ∣ γ 1 0) :
    (lowerConj ℓ γ hγ) 1 0 = γ 1 0 / ℓ := rfl

theorem lowerConj_apply_zero_zero (γ : SL(2, ℤ)) (hγ : (ℓ : ℤ) ∣ γ 1 0) :
    (lowerConj ℓ γ hγ) 0 0 = γ 0 0 := rfl

theorem lowerConj_apply_zero_one (γ : SL(2, ℤ)) (hγ : (ℓ : ℤ) ∣ γ 1 0) :
    (lowerConj ℓ γ hγ) 0 1 = ℓ * γ 0 1 := rfl

theorem lowerConj_apply_one_one (γ : SL(2, ℤ)) (hγ : (ℓ : ℤ) ∣ γ 1 0) :
    (lowerConj ℓ γ hγ) 1 1 = γ 1 1 := rfl

theorem heckeDiag_mul (hℓ : ℓ ≠ 0) (γ : SL(2, ℤ)) (hγ : (ℓ : ℤ) ∣ γ 1 0) :
    heckeDiagMatrix ℓ * (γ : GL (Fin 2) ℝ) =
      ((lowerConj ℓ γ hγ : SL(2, ℤ)) : GL (Fin 2) ℝ) * heckeDiagMatrix ℓ := by
  obtain ⟨c, hc⟩ := hγ
  have h0 : (ℓ : ℤ) ≠ 0 := by exact_mod_cast hℓ
  have h10 : ((lowerConj ℓ γ ⟨c, hc⟩ : SL(2, ℤ)) 1 0 : ℤ) = c := by
    rw [lowerConj_apply_one_zero, hc, Int.mul_ediv_cancel_left _ h0]
  ext i j
  simp only [Units.val_mul, val_heckeDiagMatrix hℓ]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, lowerConj_apply_zero_zero, lowerConj_apply_one_one,
      lowerConj_apply_zero_one, h10, hc, mul_comm]

theorem Gamma0_mul_le_conj (hℓ : ℓ ≠ 0) :
    ((CongruenceSubgroup.Gamma0 (N * ℓ) : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) ≤
      toConjAct (heckeDiagMatrix ℓ)⁻¹ •
        ((CongruenceSubgroup.Gamma0 N : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) := by
  rintro x ⟨γ, hγ, rfl⟩
  rw [toConjAct_inv, Subgroup.mem_inv_pointwise_smul_iff, ConjAct.toConjAct_smul]
  have hγ' : ((N : ℤ) * ℓ) ∣ γ 1 0 := by
    have := (CongruenceSubgroup.Gamma0_mem).mp hγ
    have h := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp this
    exact_mod_cast h
  have hℓγ : (ℓ : ℤ) ∣ γ 1 0 := (dvd_mul_left _ _).trans hγ'
  refine ⟨lowerConj ℓ γ hℓγ, ?_, ?_⟩
  · rw [SetLike.mem_coe, CongruenceSubgroup.Gamma0_mem, lowerConj_apply_one_zero,
      ZMod.intCast_zmod_eq_zero_iff_dvd]
    obtain ⟨c, hc⟩ := hγ'
    rw [hc, show (N : ℤ) * ℓ * c = ℓ * (N * c) by ring,
      Int.mul_ediv_cancel_left _ (by exact_mod_cast hℓ)]
    exact_mod_cast dvd_mul_right _ _
  · rw [eq_mul_inv_iff_mul_eq]
    exact (heckeDiag_mul ℓ hℓ γ hℓγ).symm

def shift [NeZero ℓ] {k : ℤ} (g : ModularForm (CongruenceSubgroup.Gamma0 N) k) :
    ModularForm (CongruenceSubgroup.Gamma0 (N * ℓ)) k :=
  haveI : ((CongruenceSubgroup.Gamma0 (N * ℓ) : Subgroup SL(2, ℤ)) :
      Subgroup (GL (Fin 2) ℝ)).HasDetPlusMinusOne := inferInstance
  restrict (Gamma0_mul_le_conj N ℓ (NeZero.ne ℓ)) (ModularForm.translate g (heckeDiagMatrix ℓ))

theorem shift_apply [NeZero ℓ] {k : ℤ} (g : ModularForm (CongruenceSubgroup.Gamma0 N) k)
    (τ : ℍ) : shift N ℓ g τ = (ℓ : ℂ) ^ (k - 1) * g (heckeDiagMatrix ℓ • τ) := by
  rw [← slash_heckeDiagMatrix_apply k (NeZero.ne ℓ)]
  rfl

variable {N ℓ}

theorem qParam_heckeDiag_smul (hℓ : ℓ ≠ 0) (τ : ℍ) :
    Function.Periodic.qParam 1 ((heckeDiagMatrix ℓ • τ : ℍ) : ℂ) =
      Function.Periodic.qParam 1 (τ : ℂ) ^ ℓ := by
  simp only [Function.Periodic.qParam]
  rw [coe_heckeDiagMatrix_smul hℓ, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

def shiftCoeff (ℓ : ℕ) (k : ℤ) (a : ℕ → ℂ) (m : ℕ) : ℂ :=
  if ℓ ∣ m then (ℓ : ℂ) ^ (k - 1) * a (m / ℓ) else 0

theorem hasSum_shift [NeZero N] [NeZero ℓ] {k : ℤ}
    (g : ModularForm (CongruenceSubgroup.Gamma0 N) k) (τ : ℍ) :
    HasSum (fun m : ℕ => shiftCoeff ℓ k (fun n => (qExpansion 1 g).coeff n) m •
      Function.Periodic.qParam 1 (τ : ℂ) ^ m) (shift N ℓ g τ) := by
  have hℓ := NeZero.ne ℓ
  have h1 := hasSum_qExpansion one_pos
    (SlashInvariantFormClass.periodic_comp_ofComplex g (by simp : (1 : ℝ) ∈ _))
    (ModularFormClass.holo g) (ModularFormClass.bdd_at_infty g) (heckeDiagMatrix ℓ • τ)
  rw [qParam_heckeDiag_smul hℓ] at h1
  have h2 := h1.mul_left ((ℓ : ℂ) ^ (k - 1))
  rw [shift_apply]
  have hinj : Function.Injective (fun n : ℕ => ℓ * n) := mul_right_injective₀ hℓ
  have hsupp : ∀ m ∉ Set.range (fun n : ℕ => ℓ * n),
      shiftCoeff ℓ k (fun n => (qExpansion 1 g).coeff n) m •
        Function.Periodic.qParam 1 (τ : ℂ) ^ m = 0 := by
    intro m hm
    have hd : ¬ ℓ ∣ m := fun ⟨n, hn⟩ => hm ⟨n, hn.symm⟩
    simp [shiftCoeff, hd]
  refine (hinj.hasSum_iff hsupp).mp ?_
  convert h2 using 1 <;> try rfl
  ext n
  simp only [Function.comp_apply, shiftCoeff, dvd_mul_right, if_true,
    Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hℓ), smul_eq_mul, pow_mul]
  ring

theorem qExpansion_shift_coeff [NeZero N] [NeZero ℓ] {k : ℤ}
    (g : ModularForm (CongruenceSubgroup.Gamma0 N) k) (m : ℕ) :
    (qExpansion 1 (shift N ℓ g)).coeff m =
      shiftCoeff ℓ k (fun n => (qExpansion 1 g).coeff n) m :=
  (ModularFormClass.qExpansion_coeff_unique one_pos (by simp) (f := shift N ℓ g)
    (hasSum_shift g) m).symm

theorem coe_qExpansion_shift [NeZero N] [NeZero ℓ] {k : ℤ}
    (g : ModularForm (CongruenceSubgroup.Gamma0 N) k) :
    ((qExpansion 1 (shift N ℓ g) : PowerSeries ℂ) : LaurentSeries ℂ) =
      HahnSeries.C ((ℓ : ℂ) ^ (k - 1)) *
        ModularCurve.qExpand ℂ ℓ ((qExpansion 1 g : PowerSeries ℂ) : LaurentSeries ℂ) := by
  have hℓ := NeZero.ne ℓ
  rw [HahnSeries.C_mul_eq_smul]
  ext m
  rw [HahnSeries.coeff_smul, PowerSeries.coeff_coe, smul_eq_mul]
  by_cases hd : (ℓ : ℤ) ∣ m
  · obtain ⟨n, rfl⟩ := hd
    rw [ModularCurve.qExpand_coeff_mul, PowerSeries.coeff_coe]
    by_cases hn : n < 0
    · have : (ℓ : ℤ) * n < 0 := by
        have : (0 : ℤ) < ℓ := by exact_mod_cast Nat.pos_of_ne_zero hℓ
        nlinarith
      rw [if_pos this, if_pos hn, mul_zero]
    · have hn' : 0 ≤ n := le_of_not_gt hn
      have : ¬ (ℓ : ℤ) * n < 0 := not_lt.mpr (by positivity)
      rw [if_neg this, if_neg hn, qExpansion_shift_coeff, shiftCoeff, Int.natAbs_mul,
        Int.natAbs_natCast, if_pos (dvd_mul_right _ _),
        Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hℓ)]
  · rw [ModularCurve.qExpand_coeff_of_not_dvd ℓ _ hd, mul_zero]
    split_ifs with hm
    · rfl
    · rw [qExpansion_shift_coeff, shiftCoeff, if_neg]
      intro h
      apply hd
      have hm' : (m : ℤ) = (m.natAbs : ℕ) := (Int.natAbs_of_nonneg (le_of_not_gt hm)).symm
      rw [hm']
      exact_mod_cast h

theorem coe_eq_zero_iff {k : ℤ} (f : ModularForm (CongruenceSubgroup.Gamma0 N) k) :
    (f : ℍ → ℂ) = 0 ↔ f = 0 := by
  constructor
  · intro h
    exact DFunLike.coe_injective (h.trans (ModularForm.coe_zero).symm)
  · rintro rfl; rfl

theorem eventually_ne_zero {k : ℤ} (f : ModularForm (CongruenceSubgroup.Gamma0 N) k)
    (hf : f ≠ 0) (τ : ℍ) : ∀ᶠ w in 𝓝[≠] τ, (f : ℍ → ℂ) w ≠ 0 := by
  by_contra hcon
  have hfr : ∃ᶠ w in 𝓝[≠] τ, (f : ℍ → ℂ) w = 0 := by
    simpa [Filter.not_eventually] using hcon
  exact hf ((coe_eq_zero_iff f).mp (eq_zero_of_frequently (ModularFormClass.holo f) hfr))

variable (ℓ) in

theorem map_heckeDiag_smul_nhdsNE (τ : ℍ) :
    Filter.map (fun z : ℍ => heckeDiagMatrix ℓ • z) (𝓝[≠] τ) = 𝓝[≠] (heckeDiagMatrix ℓ • τ) :=
  (Homeomorph.smul (heckeDiagMatrix ℓ) : ℍ ≃ₜ ℍ).map_punctured_nhds_eq τ

theorem map_coe_nhdsNE (τ : ℍ) :
    Filter.map ((↑) : ℍ → ℂ) (𝓝[≠] τ) = 𝓝[≠] (τ : ℂ) := by
  have h := isOpenEmbedding_coe.map_nhdsWithin_preimage_eq ({(τ : ℂ)}ᶜ) τ
  have hpre : ((↑) : ℍ → ℂ) ⁻¹' ({(τ : ℂ)}ᶜ : Set ℂ) = ({τ}ᶜ : Set ℍ) := by
    ext w
    simp
  rwa [hpre] at h

theorem eventually_nhdsNE_coe_iff {p : ℍ → Prop} {τ : ℍ} :
    (∀ᶠ z in 𝓝[≠] (τ : ℂ), p (ofComplex z)) ↔ ∀ᶠ w in 𝓝[≠] τ, p w := by
  rw [← map_coe_nhdsNE, Filter.eventually_map]
  simp only [ofComplex_apply]

theorem isBoundedUnder_congr {α : Type*} {l : Filter α} {u v : α → ℝ} (h : u =ᶠ[l] v) :
    IsBoundedUnder (· ≤ ·) l u ↔ IsBoundedUnder (· ≤ ·) l v :=
  ⟨fun hu => hu.mono_le h.symm.le, fun hv => hv.mono_le h.le⟩

theorem mem_restrictAlong_iff {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F]
    [Algebra K F'] (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (w : Place K F') (x : F) :
    x ∈ (w.restrictAlong φ hφ).toValuationSubring ↔ φ x ∈ w.toValuationSubring :=
  Iff.rfl

variable (ℓ) in

theorem realize_qExpand_eventuallyEq [NeZero N] [NeZero ℓ] (x : LaurentSeries ℂ)
    (hx : x ∈ laurentBaseChange ℂ (modularFunctionFieldFull N)) (τ : ℍ) :
    (fun z : ℍ => realize (N * ℓ) (qExpand ℂ ℓ x) z) =ᶠ[𝓝[≠] τ]
      fun z : ℍ => realize N x (heckeDiagMatrix ℓ • z) := by
  obtain ⟨k, g, h, hh, hgh⟩ :=
    exists_modularForm_mul_qExpansion_eq_of_mem_laurentBaseChange N x hx
  have hℓ : (ℓ : ℂ) ^ (k - 1) ≠ 0 := zpow_ne_zero _ (by exact_mod_cast NeZero.ne ℓ)

  have hgh' : qExpand ℂ ℓ x *
      ((qExpansion 1 (shift N ℓ h : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) =
        ((qExpansion 1 (shift N ℓ g : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) := by
    rw [coe_qExpansion_shift, coe_qExpansion_shift, mul_left_comm, ← map_mul, hgh]

  have hev : ∀ᶠ z in 𝓝[≠] τ, (h : ℍ → ℂ) (heckeDiagMatrix ℓ • z) ≠ 0 := by
    have := eventually_ne_zero h hh (heckeDiagMatrix ℓ • τ)
    rw [← map_heckeDiag_smul_nhdsNE ℓ τ, Filter.eventually_map] at this
    exact this
  filter_upwards [hev] with z hz
  have hz' : (shift N ℓ h : ℍ → ℂ) z ≠ 0 := by
    rw [shift_apply]; exact mul_ne_zero hℓ hz
  rw [realize_eq_div (N * ℓ) (shift N ℓ g) (shift N ℓ h) _ hgh' z hz',
    realize_eq_div N g h x hgh _ hz, shift_apply, shift_apply, mul_div_mul_left _ _ hℓ]

end ModularCurve.RestrictAlongPtHeckeBetaBar
p2m_reactivate "P2MW.S_ModularCurve_ComplexPlaceDictionary_restrictAlong_pt_heckeBetaBar.ModularCurve P2MW.S_ModularCurve_ComplexPlaceDictionary_restrictAlong_pt_heckeBetaBar.ModularCurve.RestrictAlongPtHeckeBetaBar"
p2m_reactivate "P2MW.S_ModularCurve_ComplexPlaceDictionary_restrictAlong_pt_heckeBetaBar.ModularCurve"

end
p2m_reactivate "P2MW.S_ModularCurve_ComplexPlaceDictionary_restrictAlong_pt_heckeBetaBar.ModularCurve P2MW.S_ModularCurve_ComplexPlaceDictionary_restrictAlong_pt_heckeBetaBar.ModularCurve.RestrictAlongPtHeckeBetaBar"

open UpperHalfPlane _root_.ModularCurve _root_.P2MW.S_ModularCurve_ComplexPlaceDictionary_restrictAlong_pt_heckeBetaBar.ModularCurve AlgebraicCurve ModularCurve.RestrictAlongPtHeckeBetaBar Filter in
open scoped Topology in
theorem solution
    {N : ℕ} [NeZero N] (ℓ : ℕ) [NeZero ℓ] (D : ModularCurve.ComplexPlaceDictionary N)
    (D' : ModularCurve.ComplexPlaceDictionary (N * ℓ))
    (hβ : ModularCurve.HeckeBetaBarIntegral ℂ N ℓ) (τ : UpperHalfPlane) :
    (D'.pt τ).restrictAlong (ModularCurve.heckeBetaBar ℂ N ℓ) hβ =
        D.pt (ModularForm.heckeDiagMatrix ℓ • τ) ∧
      D'.ramification τ *
          (D'.pt τ).ramificationIndexAlong (ModularCurve.heckeBetaBar ℂ N ℓ) =
        D.ramification (ModularForm.heckeDiagMatrix ℓ • τ) := by

  have h1 : (D'.pt τ).restrictAlong (heckeBetaBar ℂ N ℓ) hβ =
      D.pt (ModularForm.heckeDiagMatrix ℓ • τ) := by
    apply Place.ext
    ext x
    rw [mem_restrictAlong_iff, D'.mem_pt_iff, D.mem_pt_iff, coe_heckeBetaBar]
    have h : (fun z : ℍ => ‖realize (N * ℓ) (qExpand ℂ ℓ (x : LaurentSeries ℂ)) z‖) =ᶠ[𝓝[≠] τ]
        fun z : ℍ => ‖realize N (x : LaurentSeries ℂ) (ModularForm.heckeDiagMatrix ℓ • z)‖ :=
      (realize_qExpand_eventuallyEq ℓ (x : LaurentSeries ℂ) x.2 τ).fun_comp (‖·‖)
    rw [isBoundedUnder_congr h, ← map_heckeDiag_smul_nhdsNE ℓ τ]
    exact Filter.isBoundedUnder_map_iff.symm
  refine ⟨h1, ?_⟩

  set w := ModularForm.heckeDiagMatrix ℓ • τ with hw
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible (D.pt w).toValuationSubring
  set x : laurentBaseChange ℂ (modularFunctionFieldFull N) :=
    (π : laurentBaseChange ℂ (modularFunctionFieldFull N)) with hx
  have hordx : (D.pt w).ord x = 1 := (D.pt w).ord_coe_irreducible hπ
  have hx0 : x ≠ 0 := by
    intro h0
    rw [h0, Place.ord_zero] at hordx
    exact zero_ne_one hordx
  have hβx0 : heckeBetaBar ℂ N ℓ x ≠ 0 := (map_ne_zero _).mpr hx0

  have hA := D'.meromorphicOrderAt_realize τ (heckeBetaBar ℂ N ℓ x) hβx0
  rw [Place.ord_restrictAlong (heckeBetaBar ℂ N ℓ) hβ, h1, hordx, mul_one] at hA

  have hB := D.meromorphicOrderAt_realize w x hx0
  rw [hordx, mul_one] at hB

  have hev : (fun z : ℂ => realize (N * ℓ) ((heckeBetaBar ℂ N ℓ x : _) : LaurentSeries ℂ)
      (ofComplex z)) =ᶠ[𝓝[≠] (τ : ℂ)]
        fun z : ℂ => realize N (x : LaurentSeries ℂ)
          (ModularForm.heckeDiagMatrix ℓ • ofComplex z) := by
    rw [coe_heckeBetaBar]
    exact (eventually_nhdsNE_coe_iff (p := fun v : ℍ =>
      realize (N * ℓ) (qExpand ℂ ℓ (x : LaurentSeries ℂ)) v =
        realize N (x : LaurentSeries ℂ) (ModularForm.heckeDiagMatrix ℓ • v))).mpr
      (realize_qExpand_eventuallyEq ℓ (x : LaurentSeries ℂ) x.2 τ)
  have hcomp := UpperHalfPlane.meromorphicOrderAt_comp_smul
    (f := fun v : ℍ => realize N (x : LaurentSeries ℂ) v) (τ := τ)
    (g := ModularForm.heckeDiagMatrix ℓ)
    (by rw [← Matrix.GeneralLinearGroup.val_det_apply]; exact ModularForm.det_heckeDiagMatrix_pos ℓ)
  rw [meromorphicOrderAt_congr hev, hcomp, ← hw, hB] at hA
  have := WithTop.coe_injective hA
  exact_mod_cast this.symm

end S_ModularCurve_ComplexPlaceDictionary_restrictAlong_pt_heckeBetaBar
end P2MW
export P2MW.S_ModularCurve_ComplexPlaceDictionary_restrictAlong_pt_heckeBetaBar (solution)
