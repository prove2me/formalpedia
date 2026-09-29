-- Prove2me | solution 1 for ModularCurve.exists_slash_fricke_eq_sum_smul_of_ratCast_qExpansion
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/b9b7d2a1-36fe-5a8d-b22a-9191ec2d175b

import Mathlib
import Definitions.Def_ModularCurve_XH
import Definitions.Def_CohCarrier_Inst
import Definitions.Def_CohCarrier_Fricke
import Theorems.Thm_ModularCurve_exists_qExpansion_slash_fricke_eq_and_conj_eq_slash_gamma0
import Theorems.Thm_PowerSeries_exists_map_eq_sum_smul_map_of_forall_map_algEquiv_mem
import Theorems.Thm_ModularCurve_exists_isIntegralQExp_smul_of_ratCast_qExpansion
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_slash_fricke_eq_sum_smul_of_ratCast_qExpansion

set_option autoImplicit false

noncomputable section

namespace A2FRS

open UpperHalfPlane CongruenceSubgroup ModularCurve Matrix IntermediateField HahnSeries

open scoped MatrixGroups ModularForm Pointwise

section Groups

variable {M : ℕ} {H : Subgroup (ZMod M)ˣ}

abbrev ΓGL (Γ : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ) :=
  ((Γ : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

theorem one_mem_strictPeriods_of_T_mem {Γ : Subgroup SL(2, ℤ)} (hT : ModularGroup.T ∈ Γ) :
    (1 : ℝ) ∈ (ΓGL Γ).strictPeriods := by
  rw [Subgroup.strictPeriods_eq_zmultiples_one_of_T_mem hT]
  exact AddSubgroup.mem_zmultiples _

variable (M) in

def frickeGL [NeZero M] : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![(0 : ℝ), -1; (M : ℝ), 0]
    (by rw [Matrix.det_fin_two_of]; simp [NeZero.ne M])

@[scoped simp]
theorem val_frickeGL [NeZero M] :
    ((frickeGL M : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = !![(0 : ℝ), -1; (M : ℝ), 0] := rfl

theorem det_frickeGL [NeZero M] : ((frickeGL M).det : ℝ) = M := by
  rw [Matrix.GeneralLinearGroup.val_det_apply, val_frickeGL, Matrix.det_fin_two_of]; ring

theorem det_frickeGL_pos [NeZero M] : 0 < ((frickeGL M).det : ℝ) := by
  rw [det_frickeGL]; exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne M)

theorem eq_frickeGL [NeZero M] {W : GL (Fin 2) ℝ}
    (hW : (W : Matrix (Fin 2) (Fin 2) ℝ) = !![(0 : ℝ), -1; (M : ℝ), 0]) : W = frickeGL M :=
  Units.ext (by rw [hW]; rfl)

theorem mapGL_eq_coe (γ : SL(2, ℤ)) : Matrix.SpecialLinearGroup.mapGL ℝ γ = (γ : GL (Fin 2) ℝ) := rfl

theorem frickeGL_mul_mul_inv [NeZero M] (γ : SL(2, ℤ)) (h : (M : ℤ) ∣ γ 1 0) :
    frickeGL M * Matrix.SpecialLinearGroup.mapGL ℝ γ * (frickeGL M)⁻¹ =
      Matrix.SpecialLinearGroup.mapGL ℝ (CohCarrier.frickeMat M γ h) := by
  rw [mul_inv_eq_iff_eq_mul, mapGL_eq_coe, mapGL_eq_coe]
  ext i j
  have hM : (M : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne M
  obtain ⟨c, hc⟩ := h
  have hc' : (γ 1 0 / M : ℤ) = c := by rw [hc, Int.mul_ediv_cancel_left _ (by exact_mod_cast NeZero.ne M)]
  fin_cases i <;> fin_cases j <;>
    (simp [Matrix.mul_apply, Fin.sum_univ_two, CohCarrier.frickeMat, hc]; try ring)

theorem le_conj_frickeGL [NeZero M] :
    ΓGL (CohCarrier.GammaH M H) ≤ ConjAct.toConjAct (frickeGL M)⁻¹ • ΓGL (CohCarrier.GammaH M H) := by
  rintro x ⟨δ, hδ, rfl⟩
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← ConjAct.toConjAct_inv, inv_inv,
    ConjAct.toConjAct_smul]
  have h10 := CohCarrier.N_dvd_of_mem_GammaH M H ⟨δ, hδ⟩
  exact ⟨CohCarrier.frickeMat M δ h10, CohCarrier.frickeMat_mem M H ⟨δ, hδ⟩,
    (frickeGL_mul_mul_inv δ h10).symm⟩

def frickeForm [NeZero M] {k : ℤ} (f : ModularForm (ΓGL (CohCarrier.GammaH M H)) k) :
    ModularForm (ΓGL (CohCarrier.GammaH M H)) k :=
  restrictForm le_conj_frickeGL (ModularForm.translate f (frickeGL M))

@[scoped simp]
theorem coe_frickeForm [NeZero M] {k : ℤ} (f : ModularForm (ΓGL (CohCarrier.GammaH M H)) k) :
    ⇑(frickeForm f) = ⇑f ∣[k] frickeGL M := rfl

omit H in

theorem coe_smul_form {Γ : Subgroup SL(2, ℤ)} {k : ℤ} (c : ℂ) (f : ModularForm (ΓGL Γ) k) :
    ⇑(c • f) = c • ⇑f := by
  first | rfl | simp

theorem le_conj_gamma0 {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 M) :
    ΓGL (CohCarrier.GammaH M H) ≤ ConjAct.toConjAct ((γ : GL (Fin 2) ℝ))⁻¹ • ΓGL (CohCarrier.GammaH M H) := by
  rintro x ⟨δ, hδ, rfl⟩
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← ConjAct.toConjAct_inv, inv_inv,
    ConjAct.toConjAct_smul]
  exact ⟨γ * δ * γ⁻¹, CohCarrier.conj_mem_GammaH M H ⟨γ, hγ⟩ ⟨δ, hδ⟩, by simp; rfl⟩

def slashForm {k : ℤ} (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M) (f : ModularForm (ΓGL (CohCarrier.GammaH M H)) k) :
    ModularForm (ΓGL (CohCarrier.GammaH M H)) k :=
  restrictForm (le_conj_gamma0 hγ) (ModularForm.translate f (γ : GL (Fin 2) ℝ))

@[scoped simp]
theorem coe_slashForm {k : ℤ} (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M) (f : ModularForm (ΓGL (CohCarrier.GammaH M H)) k) :
    ⇑(slashForm γ hγ f) = ⇑f ∣[k] (γ : GL (Fin 2) ℝ) := rfl

end Groups

section Cyclo

local notation "Qb" => AlgebraicClosure ℚ

scoped instance isAlgebraicQbar : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) :=
  AlgebraicClosure.isAlgebraic ℚ

scoped instance isAlgClosureQbar : IsAlgClosure ℚ (AlgebraicClosure ℚ) := ⟨inferInstance, inferInstance⟩

scoped instance isGaloisQbar : IsGalois ℚ (AlgebraicClosure ℚ) :=
  IsAlgClosure.isGalois ℚ (AlgebraicClosure ℚ)

variable (M : ℕ) [NeZero M]

theorem exists_isPrimitiveRoot : ∃ ζ : Qb, IsPrimitiveRoot ζ M := by
  have hdeg : (Polynomial.cyclotomic M Qb).degree ≠ 0 := by
    rw [Polynomial.degree_cyclotomic]
    exact_mod_cast (Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne M))).ne'
  obtain ⟨ζ, hζ⟩ := IsAlgClosed.exists_root _ hdeg
  exact ⟨ζ, Polynomial.isRoot_cyclotomic_iff.mp hζ⟩

variable {M}

omit [NeZero M] in

theorem pow_eq_pow_mod {ζ : Qb} (hζ : ζ ^ M = 1) (n : ℕ) : ζ ^ n = ζ ^ (n % M) := by
  conv_lhs => rw [← Nat.div_add_mod n M, _root_.pow_add, _root_.pow_mul, hζ, one_pow, one_mul]

variable (M) in

theorem exists_coprime_forall_pow (σ : Qb ≃ₐ[ℚ] Qb) :
    ∃ c : ℕ, c.Coprime M ∧ ∀ ζ : Qb, ζ ^ M = 1 → σ ζ = ζ ^ c := by
  obtain ⟨ζ₀, h0⟩ := exists_isPrimitiveRoot M
  have h1 : (σ ζ₀) ^ M = 1 := by rw [← map_pow, h0.pow_eq_one, map_one]
  obtain ⟨c, -, hc⟩ := h0.eq_pow_of_pow_eq_one h1
  have hprim : IsPrimitiveRoot (σ ζ₀) M := h0.map_of_injective σ.injective
  rw [← hc] at hprim
  have hcop : c.Coprime M := (h0.pow_iff_coprime (Nat.pos_of_ne_zero (NeZero.ne M)) c).mp hprim
  refine ⟨c, hcop, fun ζ hζ => ?_⟩
  obtain ⟨j, -, rfl⟩ := h0.eq_pow_of_pow_eq_one hζ
  rw [map_pow, ← hc, ← pow_mul, ← pow_mul, mul_comm]

variable (M) in

theorem exists_intermediateField_of_fixed :
    ∃ K : IntermediateField ℚ Qb, FiniteDimensional ℚ K ∧
      ∀ x : Qb, (∀ σ : Qb ≃ₐ[ℚ] Qb, (∀ ζ : Qb, ζ ^ M = 1 → σ ζ = ζ) → σ x = x) → x ∈ K := by
  obtain ⟨ζ₀, h0⟩ := exists_isPrimitiveRoot M
  refine ⟨IntermediateField.adjoin ℚ {ζ₀},
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral ζ₀), fun x hx => ?_⟩
  rw [← InfiniteGalois.fixedField_fixingSubgroup (IntermediateField.adjoin ℚ {ζ₀}),
    IntermediateField.mem_fixedField_iff]
  intro σ hσ
  apply hx σ
  intro ζ hζ
  have hfix : σ ζ₀ = ζ₀ := (IntermediateField.mem_fixingSubgroup_iff _ _).mp hσ ζ₀
    (IntermediateField.mem_adjoin_simple_self ℚ ζ₀)
  obtain ⟨j, -, rfl⟩ := h0.eq_pow_of_pow_eq_one hζ
  rw [map_pow, hfix]

end Cyclo

section Span

local notation "Qb" => AlgebraicClosure ℚ

variable {M : ℕ} [NeZero M] {H : Subgroup (ZMod M)ˣ}

def res1 {k : ℤ} (f : ModularForm (ΓGL (CohCarrier.GammaH M H)) k) :
    ModularForm (Gamma1 M : Subgroup (GL (Fin 2) ℝ)) k :=
  restrictForm (Subgroup.map_mono (Gamma1_le_GammaH M H)) f

omit [NeZero M] in
@[scoped simp] theorem coe_res1 {k : ℤ} (f : ModularForm (ΓGL (CohCarrier.GammaH M H)) k) :
    ⇑(res1 f) = ⇑f := rfl

def qExpSubmodule (M : ℕ) (H : Subgroup (ZMod M)ˣ) (k : ℤ) : Submodule ℂ (PowerSeries ℂ) where
  carrier := {P | ∃ f : ModularForm (ΓGL (CohCarrier.GammaH M H)) k, qExpansion 1 ⇑f = P}
  add_mem' := by
    rintro _ _ ⟨f, rfl⟩ ⟨g, rfl⟩
    refine ⟨f + g, ?_⟩
    rw [ModularForm.coe_add, ModularForm.qExpansion_add one_pos
      (one_mem_strictPeriods_of_T_mem (translation_mem_GammaH M H))]
  zero_mem' := ⟨0, by rw [ModularForm.coe_zero, qExpansion_zero]⟩
  smul_mem' := by
    rintro c _ ⟨f, rfl⟩
    refine ⟨c • f, ?_⟩
    rw [coe_smul_form, ModularForm.qExpansion_smul one_pos
      (one_mem_strictPeriods_of_T_mem (translation_mem_GammaH M H))]

omit [NeZero M] in
theorem mem_qExpSubmodule_iff {k : ℤ} {P : PowerSeries ℂ} :
    P ∈ qExpSubmodule M H k ↔ ∃ f : ModularForm (ΓGL (CohCarrier.GammaH M H)) k, qExpansion 1 ⇑f = P :=
  Iff.rfl

theorem exists_gamma0_lowerRight (d : (ZMod M)ˣ) :
    ∃ γ : SL(2, ℤ), ∃ _ : γ ∈ Gamma0 M, ((γ 1 1 : ℤ) : ZMod M) = d := by
  obtain ⟨γd, hγd⟩ := CohCarrier.gamma0Units_surjective M d
  refine ⟨γd, γd.2, ?_⟩
  have := congrArg (fun u : (ZMod M)ˣ => (u : ZMod M)) hγd
  simpa [CohCarrier.gamma0Units, Gamma0Map] using this

def qExpL (M : ℕ) (H : Subgroup (ZMod M)ˣ) (k : ℤ) :
    ModularForm (ΓGL (CohCarrier.GammaH M H)) k →ₗ[ℂ] PowerSeries ℂ where
  toFun f := qExpansion 1 ⇑f
  map_add' f g := by
    rw [ModularForm.coe_add, ModularForm.qExpansion_add one_pos
      (one_mem_strictPeriods_of_T_mem (translation_mem_GammaH M H))]
  map_smul' c f := by
    rw [RingHom.id_apply, coe_smul_form, ModularForm.qExpansion_smul one_pos
      (one_mem_strictPeriods_of_T_mem (translation_mem_GammaH M H))]

omit [NeZero M] in
theorem qExpL_apply {k : ℤ} (f : ModularForm (ΓGL (CohCarrier.GammaH M H)) k) :
    qExpL M H k f = qExpansion 1 ⇑f := rfl

omit [NeZero M] in
theorem qExpL_injective {k : ℤ} : Function.Injective (qExpL M H k) := by
  intro f g h
  have h0 : qExpL M H k (f - g) = 0 := by rw [map_sub, h, sub_self]
  rw [qExpL_apply, ModularForm.coe_sub] at h0
  have := (ModularForm.qExpansion_eq_zero_iff one_pos
    (one_mem_strictPeriods_of_T_mem (translation_mem_GammaH M H)) (f - g)).mp
    (by rw [ModularForm.coe_sub]; exact h0)
  exact sub_eq_zero.mp this

variable (ι : Qb →+* ℂ)

theorem exists_slash_frickeGL_eq_sum {k : ℤ} (f : ModularForm (ΓGL (CohCarrier.GammaH M H)) k)
    (hfrat : ∀ n : ℕ, ∃ r : ℚ, (qExpansion 1 ⇑f).coeff n = (r : ℂ)) :
    ∃ (n : ℕ) (c : Fin n → Qb) (g : Fin n → ModularForm (ΓGL (CohCarrier.GammaH M H)) k)
      (p : Fin n → PowerSeries ℤ), (∀ i, IsIntegralQExp (g i) (p i)) ∧
        (⇑f : ℍ → ℂ) ∣[k] frickeGL M = ∑ i, ι (c i) • (⇑(g i) : ℍ → ℂ) := by

  obtain ⟨a, ha1, ha2⟩ :=
    ModularCurve.exists_qExpansion_slash_fricke_eq_and_conj_eq_slash_gamma0 M (res1 f) hfrat ι
      (frickeGL M) val_frickeGL
  simp only [coe_res1] at ha1 ha2
  set A : PowerSeries Qb := PowerSeries.mk a with hA
  have hAmap : A.map ι = qExpansion 1 (⇑f ∣[k] frickeGL M) := by
    ext n; rw [PowerSeries.coeff_map, hA, PowerSeries.coeff_mk, ha1]

  obtain ⟨K, hKfin, hKmem⟩ := exists_intermediateField_of_fixed M
  haveI := hKfin
  have hAK : ∀ n, PowerSeries.coeff n A ∈ K := by
    intro n
    rw [hA, PowerSeries.coeff_mk]
    refine hKmem (a n) fun σ hσ => ι.injective ?_
    have h1 : (1 : SL(2, ℤ)) ∈ Gamma0 M := one_mem _
    have h11 : (((1 : SL(2, ℤ)) 1 1 : ℤ) : ZMod M) = ((1 : ℕ) : ZMod M) := by simp
    have h2 := ha2 σ 1 (fun ζ hζ => by rw [pow_one]; exact hσ ζ hζ) 1 h1 h11 n
    rw [← h2, ← ha1 n]
    have e : ((1 : SL(2, ℤ)) : GL (Fin 2) ℝ) = 1 := map_one (Matrix.SpecialLinearGroup.mapGL ℝ)
    rw [e, SlashAction.slash_one]

  have hV : ∀ σ : Qb ≃ₐ[ℚ] Qb, A.map (ι.comp (σ : Qb →+* Qb)) ∈ LinearMap.range (qExpL M H k) := by
    intro σ
    obtain ⟨c, hcop, hσ⟩ := exists_coprime_forall_pow M σ
    obtain ⟨γ, hγ, hγc⟩ := exists_gamma0_lowerRight (M := M) (ZMod.unitOfCoprime c hcop)
    rw [ZMod.coe_unitOfCoprime] at hγc
    refine ⟨slashForm γ hγ (frickeForm f), ?_⟩
    ext n
    rw [qExpL_apply, coe_slashForm, coe_frickeForm, ha2 σ c hσ γ hγ hγc n, PowerSeries.coeff_map, hA,
      PowerSeries.coeff_mk, RingHom.comp_apply, RingHom.coe_coe]

  obtain ⟨n, cv, r, hrV, hsum⟩ :=
    PowerSeries.exists_map_eq_sum_smul_map_of_forall_map_algEquiv_mem ι (LinearMap.range (qExpL M H k))
      K A hAK hV

  have hR : ∀ i, ∃ (R : ModularForm (ΓGL (CohCarrier.GammaH M H)) k) (D : ℤ) (p : PowerSeries ℤ),
      D ≠ 0 ∧ IsIntegralQExp (⇑((D : ℂ) • R)) p ∧ qExpansion 1 ⇑R = (r i).map (algebraMap ℚ ℂ) := by
    intro i
    obtain ⟨R, hRq⟩ := hrV i
    rw [qExpL_apply] at hRq
    have hRrat : ∀ m : ℕ, ∃ q : ℚ, (qExpansion 1 ⇑(res1 R)).coeff m = (q : ℂ) := fun m =>
      ⟨PowerSeries.coeff m (r i), by rw [coe_res1, hRq, PowerSeries.coeff_map, eq_ratCast]⟩
    obtain ⟨D, p, hD, hp⟩ :=
      ModularCurve.exists_isIntegralQExp_smul_of_ratCast_qExpansion M (res1 R) hRrat
    exact ⟨R, D, p, hD, by rwa [coe_smul_form], hRq⟩
  choose R D p hD hp hRq using hR
  refine ⟨n, fun i => cv i / (D i : Qb), fun i => (D i : ℂ) • R i, p, hp, ?_⟩

  have hforms : frickeForm f = ∑ i, ι (cv i) • R i := by
    apply qExpL_injective
    rw [map_sum, qExpL_apply, coe_frickeForm, ← hAmap, hsum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, qExpL_apply, hRq]
  have hcoe := congrArg (fun F : ModularForm (ΓGL (CohCarrier.GammaH M H)) k => (⇑F : ℍ → ℂ)) hforms
  have hsumcoe : (⇑(∑ i, ι (cv i) • R i) : ℍ → ℂ) = ∑ i, ⇑(ι (cv i) • R i) :=
    map_sum (FunLike.coeAddMonoidHom (ModularForm (ΓGL (CohCarrier.GammaH M H)) k) ℍ ℂ) _ _
  simp only [coe_frickeForm, hsumcoe, coe_smul_form] at hcoe
  rw [hcoe]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [coe_smul_form, smul_smul, map_div₀, map_intCast, div_mul_cancel₀ _ (by exact_mod_cast hD i)]

end Span

end A2FRS
p2m_reactivate "P2MW.S_ModularCurve_exists_slash_fricke_eq_sum_smul_of_ratCast_qExpansion.A2FRS"

open scoped MatrixGroups ModularForm in
open A2FRS in
theorem solution (M : ℕ) [NeZero M]
    (H : Subgroup (ZMod M)ˣ) {k : ℤ}
    (f : ModularForm (CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ)) k)
    (hf : ∀ n : ℕ, ∃ r : ℚ, (UpperHalfPlane.qExpansion 1 f).coeff n = (r : ℂ))
    (ι : AlgebraicClosure ℚ →+* ℂ) (W : GL (Fin 2) ℝ)
    (hW : (W : Matrix (Fin 2) (Fin 2) ℝ) = !![(0 : ℝ), -1; (M : ℝ), 0]) :
    ∃ (n : ℕ) (c : Fin n → AlgebraicClosure ℚ)
      (g : Fin n → ModularForm (CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ)) k)
      (p : Fin n → PowerSeries ℤ), (∀ i, ModularCurve.IsIntegralQExp (g i) (p i)) ∧
        (⇑f : UpperHalfPlane → ℂ) ∣[k] W = ∑ i, ι (c i) • (⇑(g i) : UpperHalfPlane → ℂ) := by
  obtain rfl : W = frickeGL M := eq_frickeGL hW
  exact exists_slash_frickeGL_eq_sum ι f hf

end
p2m_reactivate "P2MW.S_ModularCurve_exists_slash_fricke_eq_sum_smul_of_ratCast_qExpansion.A2FRS"

end S_ModularCurve_exists_slash_fricke_eq_sum_smul_of_ratCast_qExpansion
end P2MW
export P2MW.S_ModularCurve_exists_slash_fricke_eq_sum_smul_of_ratCast_qExpansion (solution)
