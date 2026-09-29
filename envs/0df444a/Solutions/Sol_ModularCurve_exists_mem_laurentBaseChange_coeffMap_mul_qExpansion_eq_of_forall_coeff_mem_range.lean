-- Prove2me | solution 1 for ModularCurve.exists_mem_laurentBaseChange_coeffMap_mul_qExpansion_eq_of_forall_coeff_mem_range
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/2aab54eb-b273-5635-a370-ce8331cfb9af

import Mathlib
import Definitions.Def_ModularCurve_XH
import Definitions.Def_FLTPrelim_Modularity
import Theorems.Thm_CuspForm_exists_basis_gammaH_qCoeff_mem_range_ratCast
import Theorems.Thm_ModularCurve_exists_isIntegralQExp_smul_of_ratCast_qExpansion
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_mem_laurentBaseChange_coeffMap_mul_qExpansion_eq_of_forall_coeff_mem_range

open UpperHalfPlane ModularCurve HahnSeries

open scoped MatrixGroups ModularForm Manifold

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace R4Desc

variable {N : ℕ} [NeZero N] {H : Subgroup (ZMod N)ˣ}

variable (N H) in

abbrev Γ : Subgroup (GL (Fin 2) ℝ) := (CohCarrier.GammaH N H : Subgroup (GL (Fin 2) ℝ))

theorem one_mem_strictPeriods : (1 : ℝ) ∈ (Γ N H).strictPeriods := by
  rw [Subgroup.strictPeriods_eq_zmultiples_one_of_T_mem (translation_mem_GammaH N H)]
  exact AddSubgroup.mem_zmultiples _

theorem Γ_le_SL : Γ N H ≤ 𝒮ℒ := Subgroup.map_le_range _ _

scoped instance : (CohCarrier.GammaH N H).FiniteIndex := Subgroup.finiteIndex_of_le (Gamma1_le_GammaH N H)

def restrictCusp {Γ₁ Γ₂ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ} (h : Γ₂ ≤ Γ₁) (f : CuspForm Γ₁ k) :
    CuspForm Γ₂ k where
  toFun := f
  slash_action_eq' A hA := f.slash_action_eq' A (h hA)
  holo' := f.holo'
  zero_at_cusps' hc := f.zero_at_cusps' (hc.mono h)

@[scoped simp] theorem coe_restrictCusp {Γ₁ Γ₂ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ} (h : Γ₂ ≤ Γ₁) (f : CuspForm Γ₁ k) :
    (⇑(restrictCusp h f) : ℍ → ℂ) = f := rfl

theorem exists_cuspForm_twelve_ne_zero : ∃ c : CuspForm (Γ N H) 12, c ≠ 0 := by
  refine ⟨restrictCusp Γ_le_SL CuspForm.discriminant, fun h => ?_⟩
  have := congrArg (fun f : CuspForm (Γ N H) 12 => (⇑f : ℍ → ℂ) UpperHalfPlane.I) h
  simp only [coe_restrictCusp, CuspForm.coe_discriminant, CuspForm.coe_zero, Pi.zero_apply] at this
  exact ModularForm.discriminant_ne_zero _ this

def mulCusp {k k' : ℤ} (Φ : ModularForm (Γ N H) k) (c : CuspForm (Γ N H) k') : CuspForm (Γ N H) (k + k') where
  toFun := (⇑Φ : ℍ → ℂ) * ⇑c
  slash_action_eq' A hA := by
    rw [ModularForm.mul_slash, Subgroup.HasDetPlusMinusOne.abs_det hA, one_smul,
      SlashInvariantFormClass.slash_action_eq Φ A hA, SlashInvariantFormClass.slash_action_eq c A hA]
  holo' := Φ.holo'.mul c.holo'
  zero_at_cusps' hc γ hγ := by
    show IsZeroAtImInfty (((⇑Φ : ℍ → ℂ) * ⇑c) ∣[k + k'] γ)
    rw [ModularForm.mul_slash, IsZeroAtImInfty]
    exact Filter.ZeroAtFilter.smul _
      ((Φ.bdd_at_cusps' hc γ hγ).mul_zeroAtFilter (c.zero_at_cusps' hc γ hγ))

@[scoped simp] theorem coe_mulCusp {k k' : ℤ} (Φ : ModularForm (Γ N H) k) (c : CuspForm (Γ N H) k') :
    (⇑(mulCusp Φ c) : ℍ → ℂ) = (⇑Φ : ℍ → ℂ) * ⇑c := rfl

def qC (F : ℍ → ℂ) : LaurentSeries ℂ := ofPowerSeries ℤ ℂ (qExpansion 1 F)

theorem qC_mul_cusp {k k' : ℤ} (Φ : ModularForm (Γ N H) k) (c : CuspForm (Γ N H) k') :
    qC ((⇑Φ : ℍ → ℂ) * ⇑c) = qC Φ * qC c := by
  rw [qC, ModularForm.qExpansion_mul_coe one_pos one_mem_strictPeriods Φ c, map_mul]; rfl

theorem qC_modularForm_ne_zero {k : ℤ} {Φ : ModularForm (Γ N H) k} (hΦ : Φ ≠ 0) : qC Φ ≠ 0 := by
  rw [qC, Ne, ← map_zero (ofPowerSeries ℤ ℂ), (ofPowerSeries_injective).eq_iff,
    ModularForm.qExpansion_eq_zero_iff one_pos one_mem_strictPeriods]
  exact hΦ

theorem qC_cuspForm_ne_zero {k : ℤ} {c : CuspForm (Γ N H) k} (hc : c ≠ 0) : qC c ≠ 0 := by
  have h : (CuspForm.toModularFormₗ c : ModularForm (Γ N H) k) ≠ 0 := by
    intro h
    apply hc
    have h0 : (CuspForm.toModularFormₗ (0 : CuspForm (Γ N H) k) : ModularForm (Γ N H) k) = 0 := map_zero _
    exact CuspForm.toModularFormₗ_injective (h.trans h0.symm)
  have := qC_modularForm_ne_zero h
  exact this

theorem qC_coeff_neg (F : ℍ → ℂ) {m : ℤ} (hm : m < 0) : (qC F).coeff m = 0 :=
  ModularCurve.ofPowerSeries_coeff_of_neg _ hm

theorem qC_coeff_nat (F : ℍ → ℂ) (m : ℕ) : (qC F).coeff (m : ℤ) = (qExpansion 1 F).coeff m :=
  ofPowerSeries_apply_coeff _ _

theorem intSeriesC_coeff_neg (K : Type*) [Field K] (p : PowerSeries ℤ) {m : ℤ} (hm : m < 0) :
    (intSeriesC K p).coeff m = 0 :=
  ModularCurve.ofPowerSeries_coeff_of_neg _ hm

theorem intSeriesC_coeff_nat (K : Type*) [Field K] (p : PowerSeries ℤ) (m : ℕ) :
    (intSeriesC K p).coeff (m : ℤ) = ((PowerSeries.coeff m p : ℤ) : K) := by
  rw [intSeriesC, ofPowerSeries_apply_coeff, PowerSeries.coeff_map, eq_intCast]

def qLin (k : ℤ) : CuspForm (Γ N H) k →ₗ[ℂ] PowerSeries ℂ where
  toFun f := qExpansion 1 f
  map_add' f g := by
    rw [CuspForm.coe_add]
    exact ModularForm.qExpansion_add one_pos one_mem_strictPeriods f g
  map_smul' a f := by
    rw [CuspForm.IsGLPos.coe_smul]
    exact ModularForm.qExpansion_smul one_pos one_mem_strictPeriods a f

@[scoped simp] theorem qLin_apply {k : ℤ} (f : CuspForm (Γ N H) k) : qLin k f = qExpansion 1 f := rfl

section Retraction

variable {L : Type} [Field L] [CharZero L] (ι : L →+* ℂ)

def ratPS (F : ℍ → ℂ) (hF : ∀ n : ℕ, ModularFormClass.qCoeff F n ∈ Set.range ((↑) : ℚ → ℂ)) : PowerSeries ℚ :=
  PowerSeries.mk fun n => (hF n).choose

theorem ratPS_coeff (F : ℍ → ℂ) (hF : ∀ n : ℕ, ModularFormClass.qCoeff F n ∈ Set.range ((↑) : ℚ → ℂ))
    (n : ℕ) : ((PowerSeries.coeff n (ratPS F hF) : ℚ) : ℂ) = (qExpansion 1 F).coeff n := by
  rw [ratPS, PowerSeries.coeff_mk]
  exact (hF n).choose_spec

theorem exists_retraction :
    letI : Algebra L ℂ := ι.toAlgebra
    ∃ π : ℂ →ₗ[L] L, ∀ a : L, π (ι a) = a := by
  letI : Algebra L ℂ := ι.toAlgebra
  have hinj : LinearMap.ker (Algebra.linearMap L ℂ) = ⊥ :=
    LinearMap.ker_eq_bot.mpr (algebraMap L ℂ).injective
  obtain ⟨π, hπ⟩ := LinearMap.exists_leftInverse_of_injective (Algebra.linearMap L ℂ) hinj
  refine ⟨π, fun a => ?_⟩
  have := LinearMap.congr_fun hπ a
  exact this

theorem retraction_sum {n : ℕ} (π : letI : Algebra L ℂ := ι.toAlgebra; ℂ →ₗ[L] L)
    (hπ : ∀ a : L, π (ι a) = a) (c : Fin n → ℂ) (r : Fin n → ℚ) (z' : L)
    (hz : ι z' = ∑ i, c i * (r i : ℂ)) :
    z' = ∑ i, (r i : L) * π (c i) := by
  letI : Algebra L ℂ := ι.toAlgebra
  have h1 : ∑ i, c i * (r i : ℂ) = ∑ i, ((r i : L)) • c i := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Algebra.smul_def, RingHom.algebraMap_toAlgebra, map_ratCast, mul_comm]
  have := congrArg π hz
  rw [hπ, h1, map_sum] at this
  rw [this]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [LinearMap.map_smul, smul_eq_mul]

end Retraction

section Descent

variable {L : Type} [Field L] [CharZero L] (ι : L →+* ℂ)

theorem coeffMap_coeffEmb (x : LaurentSeries ℚ) : coeffMap ι (coeffEmb L x) = coeffMap (algebraMap ℚ ℂ) x := by
  rw [coeffEmb, coeffMap_coeffMap]
  exact coeffMap_congr (Subsingleton.elim _ _) x

variable {k : ℤ} {n : ℕ} (b : Module.Basis (Fin n) ℂ (CuspForm (Γ N H) k))
  (hb : ∀ (i : Fin n) (m : ℕ), ModularFormClass.qCoeff (b i) m ∈ Set.range ((↑) : ℚ → ℂ))
include hb

theorem exists_int_witness (i : Fin n) :
    ∃ (D : ℤ) (p : PowerSeries ℤ), D ≠ 0 ∧ IsIntegralQExp ((D : ℂ) • (⇑(b i) : ℍ → ℂ)) p := by
  have hle : ((CongruenceSubgroup.Gamma1 N : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) ≤ Γ N H :=
    Subgroup.map_mono (Gamma1_le_GammaH N H)
  let f : ModularForm ((CongruenceSubgroup.Gamma1 N : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) k :=
    restrictForm hle (CuspForm.toModularFormₗ (b i))
  have hf : ∀ m : ℕ, ∃ r : ℚ, (qExpansion 1 f).coeff m = (r : ℂ) := fun m => by
    obtain ⟨r, hr⟩ := hb i m
    exact ⟨r, hr.symm⟩
  obtain ⟨D, p, hD, hp⟩ := ModularCurve.exists_isIntegralQExp_smul_of_ratCast_qExpansion N f hf
  exact ⟨D, p, hD, hp⟩

def den (i : Fin n) : ℤ := (exists_int_witness b hb i).choose

def wit (i : Fin n) : PowerSeries ℤ := (exists_int_witness b hb i).choose_spec.choose
theorem den_ne (i : Fin n) : den b hb i ≠ 0 := (exists_int_witness b hb i).choose_spec.choose_spec.1
theorem wit_spec (i : Fin n) : IsIntegralQExp ((den b hb i : ℂ) • (⇑(b i) : ℍ → ℂ)) (wit b hb i) :=
  (exists_int_witness b hb i).choose_spec.choose_spec.2

def intForm (i : Fin n) : ModularForm (Γ N H) k := (den b hb i : ℂ) • CuspForm.toModularFormₗ (b i)

theorem coe_intForm (i : Fin n) : (⇑(intForm b hb i) : ℍ → ℂ) = (den b hb i : ℂ) • (⇑(b i) : ℍ → ℂ) := by
  rw [intForm, ModularForm.IsGLPos.coe_smul]; rfl

theorem isIntegralQExp_intForm (i : Fin n) : IsIntegralQExp (intForm b hb i) (wit b hb i) := by
  rw [coe_intForm]; exact wit_spec b hb i

theorem wit_coeff (i : Fin n) (m : ℕ) :
    ((PowerSeries.coeff m (wit b hb i) : ℤ) : ℚ) = (den b hb i : ℚ) * PowerSeries.coeff m (ratPS (⇑(b i)) (hb i)) := by
  have h1 := (wit_spec b hb i).coeff m
  rw [ModularForm.qExpansion_smul one_pos one_mem_strictPeriods (den b hb i : ℂ) (b i)] at h1
  simp only [map_smul, smul_eq_mul] at h1
  rw [← ratPS_coeff (⇑(b i)) (hb i) m] at h1
  exact_mod_cast h1

theorem intSeriesC_wit_ne (i : Fin n) : intSeriesC ℚ (wit b hb i) ≠ 0 := by
  intro h
  apply qC_cuspForm_ne_zero (b.ne_zero i)
  ext m
  rw [HahnSeries.coeff_zero]
  rcases lt_or_ge m 0 with hm | hm
  · exact qC_coeff_neg _ hm
  · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hm
    rw [qC_coeff_nat, ← ratPS_coeff (⇑(b i)) (hb i) m]
    have h2 := congrArg (fun x : LaurentSeries ℚ => x.coeff (m : ℤ)) h
    simp only [HahnSeries.coeff_zero, intSeriesC_coeff_nat, wit_coeff] at h2
    have hD : (den b hb i : ℚ) ≠ 0 := by exact_mod_cast den_ne b hb i
    have : PowerSeries.coeff m (ratPS (⇑(b i)) (hb i)) = 0 := by
      rcases mul_eq_zero.mp h2 with h3 | h3
      · exact absurd h3 hD
      · exact h3
    rw [this, Rat.cast_zero]

def gen (i : Fin n) : LaurentSeries L := coeffEmb L (intSeriesC ℚ (wit b hb i))

theorem gen_coeff_neg (i : Fin n) {m : ℤ} (hm : m < 0) : (gen (L := L) b hb i).coeff m = 0 := by
  rw [gen, coeffEmb_coeff, intSeriesC_coeff_neg _ _ hm, map_zero]

theorem gen_coeff_nat (i : Fin n) (m : ℕ) :
    (gen (L := L) b hb i).coeff (m : ℤ) = (den b hb i : L) * ((PowerSeries.coeff m (ratPS (⇑(b i)) (hb i)) : ℚ) : L) := by
  rw [gen, coeffEmb_coeff, intSeriesC_coeff_nat, wit_coeff]
  simp

theorem exists_coeffs (g : CuspForm (Γ N H) k) (hg : ∀ m : ℕ, (qExpansion 1 (⇑g)).coeff m ∈ Set.range ι) :
    ∃ a : Fin n → L, coeffMap ι (∑ i, HahnSeries.C (a i) * gen b hb i) = qC g := by
  letI : Algebra L ℂ := ι.toAlgebra
  obtain ⟨π, hπ⟩ := exists_retraction ι
  set c : Fin n → ℂ := fun i => b.repr g i with hc
  refine ⟨fun i => (den b hb i : L)⁻¹ * π (c i), ?_⟩

  have hsum : qExpansion 1 (⇑g) = ∑ i, c i • qExpansion 1 (⇑(b i)) := by
    have := congrArg (qLin k) (b.sum_repr g).symm
    rw [map_sum] at this
    simpa [qLin_apply] using this
  ext m
  rw [coeffMap_coeff, HahnSeries.coeff_sum]
  simp only [HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul, smul_eq_mul]
  rcases lt_or_ge m 0 with hm | hm
  · rw [qC_coeff_neg _ hm]
    simp [gen_coeff_neg b hb _ hm]
  · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hm
    rw [qC_coeff_nat]
    obtain ⟨z', hz'⟩ := hg m
    have hz : ι z' = ∑ i, c i * ((PowerSeries.coeff m (ratPS (⇑(b i)) (hb i)) : ℚ) : ℂ) := by
      rw [hz', hsum, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_smul, smul_eq_mul, ratPS_coeff]
    have key := retraction_sum ι π hπ c _ z' hz
    rw [← hz']
    congr 1
    rw [key]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [gen_coeff_nat]
    have hD : (den b hb i : L) ≠ 0 := by exact_mod_cast den_ne b hb i
    field_simp

theorem ratio_mem (i₀ : Fin n) (a a' : Fin n → L) :
    (∑ i, HahnSeries.C (a i) * gen b hb i) / (∑ i, HahnSeries.C (a' i) * gen b hb i)
      ∈ laurentBaseChange L (xHFunctionField N H) := by
  set K := laurentBaseChange L (xHFunctionField N H)
  have h0 : gen (L := L) b hb i₀ ≠ 0 :=
    (map_ne_zero_iff _ (RingHom.injective _)).mpr (intSeriesC_wit_ne b hb i₀)

  have hgen : ∀ i, gen (L := L) b hb i / gen b hb i₀ ∈ K := by
    intro i
    rw [gen, gen, ← map_div₀]
    refine coeffEmb_mem_laurentBaseChange L ?_
    exact div_mem_qExpFunctionFieldC (intForm b hb i) (intForm b hb i₀) (isIntegralQExp_intForm b hb i)
      (isIntegralQExp_intForm b hb i₀) (intSeriesC_wit_ne b hb i₀)
  have hC : ∀ x : L, (HahnSeries.C x : LaurentSeries L) ∈ K := fun x => by
    have e : (HahnSeries.C x : LaurentSeries L) = algebraMap L (LaurentSeries L) x := by
      rw [algebraMap_laurentSeries_eq_single L x, HahnSeries.C_apply]
    rw [e]
    exact IntermediateField.algebraMap_mem K x
  have hsum : ∀ a'' : Fin n → L, (∑ i, HahnSeries.C (a'' i) * gen b hb i) / gen b hb i₀ ∈ K := by
    intro a''
    rw [Finset.sum_div]
    refine sum_mem fun i _ => ?_
    rw [mul_div_assoc]
    exact mul_mem (hC _) (hgen i)
  have : (∑ i, HahnSeries.C (a i) * gen b hb i) / (∑ i, HahnSeries.C (a' i) * gen b hb i) =
      ((∑ i, HahnSeries.C (a i) * gen b hb i) / gen b hb i₀) /
      ((∑ i, HahnSeries.C (a' i) * gen b hb i) / gen b hb i₀) := by
    rw [div_div_div_cancel_right₀ h0]
  rw [this]
  exact div_mem (hsum a) (hsum a')

end Descent

theorem main {k : ℤ} (Φ Ψ : ModularForm (Γ N H) k) (hΨ : Ψ ≠ 0)
    (L : Type) [Field L] [CharZero L] (ι : L →+* ℂ)
    (hΦ : ∀ n : ℕ, (qExpansion 1 (⇑Φ)).coeff n ∈ Set.range ι)
    (hΨι : ∀ n : ℕ, (qExpansion 1 (⇑Ψ)).coeff n ∈ Set.range ι) :
    ∃ x : LaurentSeries L, x ∈ laurentBaseChange L (xHFunctionField N H) ∧
      coeffMap ι x * qC Ψ = qC Φ := by
  classical

  obtain ⟨n₁₂, b₁₂, hb₁₂⟩ := CuspForm.exists_basis_gammaH_qCoeff_mem_range_ratCast N H 12
  obtain ⟨c, hc⟩ := exists_cuspForm_twelve_ne_zero (N := N) (H := H)
  haveI : Nontrivial (CuspForm (Γ N H) 12) := ⟨⟨c, 0, hc⟩⟩
  obtain ⟨j₀⟩ := b₁₂.index_nonempty
  set c₀ : CuspForm (Γ N H) 12 := b₁₂ j₀ with hc₀
  have hc₀ne : c₀ ≠ 0 := b₁₂.ne_zero j₀
  have hc₀rat : ∀ m : ℕ, ∃ r : ℚ, (r : ℂ) = (qExpansion 1 (⇑c₀)).coeff m := fun m => hb₁₂ j₀ m

  have hcoef : ∀ (Θ : ModularForm (Γ N H) k), (∀ m : ℕ, (qExpansion 1 (⇑Θ)).coeff m ∈ Set.range ι) →
      ∀ m : ℕ, (qExpansion 1 (⇑(mulCusp Θ c₀))).coeff m ∈ Set.range ι := by
    intro Θ hΘ m
    rw [coe_mulCusp, ModularForm.qExpansion_mul_coe one_pos one_mem_strictPeriods Θ c₀, PowerSeries.coeff_mul]
    change _ ∈ (ι.range : Set ℂ)
    refine Subring.sum_mem ι.range fun ij _ => Subring.mul_mem _ (hΘ ij.1) ?_
    obtain ⟨r, hr⟩ := hc₀rat ij.2
    exact ⟨r, by rw [map_ratCast, hr]⟩

  obtain ⟨n, b, hb⟩ := CuspForm.exists_basis_gammaH_qCoeff_mem_range_ratCast N H (k + 12)
  obtain ⟨aΦ, haΦ⟩ := exists_coeffs ι b hb (mulCusp Φ c₀) (hcoef Φ hΦ)
  obtain ⟨aΨ, haΨ⟩ := exists_coeffs ι b hb (mulCusp Ψ c₀) (hcoef Ψ hΨι)

  have h1 : qC (⇑Ψ) ≠ 0 := qC_modularForm_ne_zero hΨ
  have h2 : qC (⇑c₀) ≠ 0 := qC_cuspForm_ne_zero hc₀ne
  have hgΨ : mulCusp Ψ c₀ ≠ 0 := by
    intro h
    have : qC (⇑(mulCusp Ψ c₀)) = 0 := by rw [h, qC, CuspForm.coe_zero, qExpansion_zero, map_zero]
    rw [coe_mulCusp, qC_mul_cusp] at this
    exact mul_ne_zero h1 h2 this
  haveI : Nontrivial (CuspForm (Γ N H) (k + 12)) := ⟨⟨mulCusp Ψ c₀, 0, hgΨ⟩⟩
  obtain ⟨i₀⟩ := b.index_nonempty
  refine ⟨_, ratio_mem b hb i₀ aΦ aΨ, ?_⟩
  rw [map_div₀, haΦ, haΨ, coe_mulCusp, coe_mulCusp, qC_mul_cusp, qC_mul_cusp]
  field_simp

end R4Desc
p2m_reactivate "P2MW.S_ModularCurve_exists_mem_laurentBaseChange_coeffMap_mul_qExpansion_eq_of_forall_coeff_mem_range.R4Desc"

end
p2m_reactivate "P2MW.S_ModularCurve_exists_mem_laurentBaseChange_coeffMap_mul_qExpansion_eq_of_forall_coeff_mem_range.R4Desc"

theorem solution
    (N : ℕ) [NeZero N] (H : Subgroup (ZMod N)ˣ) {k : ℤ}
    (Φ Ψ : ModularForm (CohCarrier.GammaH N H : Subgroup (GL (Fin 2) ℝ)) k) (hΨ : Ψ ≠ 0)
    (L : Type) [Field L] [CharZero L] (ι : L →+* ℂ)
    (hΦ : ∀ n : ℕ, (UpperHalfPlane.qExpansion 1 (⇑Φ)).coeff n ∈ Set.range ι)
    (hΨι : ∀ n : ℕ, (UpperHalfPlane.qExpansion 1 (⇑Ψ)).coeff n ∈ Set.range ι) :
    ∃ x : LaurentSeries L,
      x ∈ ModularCurve.laurentBaseChange L (ModularCurve.xHFunctionField N H) ∧
        ModularCurve.coeffMap ι x *
            HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 (⇑Ψ)) =
          HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 (⇑Φ)) :=
  R4Desc.main Φ Ψ hΨ L ι hΦ hΨι

end S_ModularCurve_exists_mem_laurentBaseChange_coeffMap_mul_qExpansion_eq_of_forall_coeff_mem_range
end P2MW
export P2MW.S_ModularCurve_exists_mem_laurentBaseChange_coeffMap_mul_qExpansion_eq_of_forall_coeff_mem_range (solution)
