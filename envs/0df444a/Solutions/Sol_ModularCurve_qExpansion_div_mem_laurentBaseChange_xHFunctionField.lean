-- Prove2me | solution 1 for ModularCurve.qExpansion_div_mem_laurentBaseChange_xHFunctionField
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/ac650516-fb70-5f76-a29c-54f86705ea4b

import Mathlib
import Definitions.Def_ModularCurve_XH
import Definitions.Def_FLTPrelim_Modularity
import Theorems.Thm_CuspForm_exists_basis_gamma1_qCoeff_mem_range_ratCast
import Theorems.Thm_ModularCurve_exists_ratCast_qExpansion_slash_of_mem_Gamma0
import Theorems.Thm_ModularCurve_exists_isIntegralQExp_smul_of_ratCast_qExpansion
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_qExpansion_div_mem_laurentBaseChange_xHFunctionField

set_option autoImplicit false

noncomputable section

open CongruenceSubgroup ModularForm UpperHalfPlane ModularCurve SlashInvariantForm
open scoped ModularForm UpperHalfPlane MatrixGroups

namespace XHRationalStructure

variable {N : ℕ} {H : Subgroup (ZMod N)ˣ} {k : ℤ}

local notation "ΓH" => CohCarrier.GammaH N H
local notation "ΓHℝ" => ((CohCarrier.GammaH N H : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))
local notation "Γ₁ℝ" => ((Gamma1 N : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

section Groups

variable (N H)

scoped instance finiteIndex_GammaH [NeZero N] : (ΓH).FiniteIndex :=
  Subgroup.finiteIndex_of_le (Gamma1_le_GammaH N H)

omit H in

theorem coe_le_SL (Γ : Subgroup SL(2, ℤ)) :
    (Γ : Subgroup (GL (Fin 2) ℝ)) ≤ 𝒮ℒ := by
  rw [MonoidHom.range_eq_map]
  exact Subgroup.map_mono le_top

theorem coeG1_le : (Γ₁ℝ) ≤ ΓHℝ := Subgroup.map_mono (Gamma1_le_GammaH N H)

theorem GammaH_le_Gamma0' : (ΓH) ≤ Gamma0 N := CohCarrier.GammaH_le_Gamma0 H

scoped instance isFiniteRelIndex_G1_GH [NeZero N] : (Γ₁ℝ).IsFiniteRelIndex ΓHℝ :=
  Subgroup.isFiniteRelIndex_of_le_right (Γ₁ℝ) (coe_le_SL (ΓH))

theorem one_mem_strictPeriods_GH : (1 : ℝ) ∈ (ΓHℝ).strictPeriods := by
  rw [Subgroup.strictPeriods_eq_zmultiples_one_of_T_mem (translation_mem_GammaH N H)]
  exact AddSubgroup.mem_zmultiples _

omit H in
theorem one_mem_strictPeriods_G1 : (1 : ℝ) ∈ (Γ₁ℝ).strictPeriods := by
  rw [CongruenceSubgroup.strictPeriods_Gamma1]
  exact AddSubgroup.mem_zmultiples _

end Groups

section Translates

theorem conj_mem_Gamma1 {γ x : SL(2, ℤ)} (hγ : γ ∈ Gamma0 N) (hx : x ∈ Gamma1 N) :
    γ * x * γ⁻¹ ∈ Gamma1 N := by
  have hx0 : x ∈ Gamma0 N := Gamma1_in_Gamma0 N hx
  have hx' : (⟨x, hx0⟩ : Gamma0 N) ∈ Gamma1' N := by
    rw [Gamma1_to_Gamma0_mem]
    exact (Gamma1_mem N x).1 hx
  haveI : (Gamma1' N).Normal := MonoidHom.normal_ker _
  have hc : (⟨γ, hγ⟩ : Gamma0 N) * ⟨x, hx0⟩ * (⟨γ, hγ⟩ : Gamma0 N)⁻¹ ∈ Gamma1' N :=
    Subgroup.Normal.conj_mem inferInstance _ hx' _
  rw [Gamma1_to_Gamma0_mem] at hc
  exact (Gamma1_mem N _).2 hc

theorem mem_coe_Gamma1_iff (x : GL (Fin 2) ℝ) :
    x ∈ (Γ₁ℝ) ↔ ∃ γ : SL(2, ℤ), γ ∈ Gamma1 N ∧ (Matrix.SpecialLinearGroup.mapGL ℝ γ) = x :=
  Subgroup.mem_map

open ConjAct Pointwise in

theorem toConjAct_inv_smul_coe_Gamma1 {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 N) :
    toConjAct (Matrix.SpecialLinearGroup.mapGL ℝ γ)⁻¹ • (Γ₁ℝ) = (Γ₁ℝ) := by
  ext x
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← map_inv, inv_inv, ConjAct.toConjAct_smul]
  constructor
  · intro h
    obtain ⟨y, hy, hyx⟩ := (mem_coe_Gamma1_iff _).1 h
    have hx : x = Matrix.SpecialLinearGroup.mapGL ℝ γ⁻¹ * Matrix.SpecialLinearGroup.mapGL ℝ y
        * Matrix.SpecialLinearGroup.mapGL ℝ γ := by
      rw [hyx, map_inv]; group
    have hmem := conj_mem_Gamma1 (Subgroup.inv_mem _ hγ) hy
    rw [inv_inv] at hmem
    rw [hx, ← map_mul, ← map_mul]
    exact Subgroup.mem_map_of_mem _ hmem
  · intro h
    obtain ⟨y, hy, rfl⟩ := (mem_coe_Gamma1_iff _).1 h
    rw [← map_inv, ← map_mul, ← map_mul]
    exact Subgroup.mem_map_of_mem _ (conj_mem_Gamma1 hγ hy)

def slashMF {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 N) (F : ModularForm (Γ₁ℝ) k) : ModularForm (Γ₁ℝ) k :=
  (ModularForm.translate F (Matrix.SpecialLinearGroup.mapGL ℝ γ)).copy
    ((⇑F : ℍ → ℂ) ∣[k] γ) rfl (toConjAct_inv_smul_coe_Gamma1 hγ).symm

@[scoped simp] theorem coe_slashMF {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 N) (F : ModularForm (Γ₁ℝ) k) :
    ⇑(slashMF hγ F) = (⇑F : ℍ → ℂ) ∣[k] γ := rfl

end Translates

section Restrict

def restrictCusp {Γ Γ' : Subgroup (GL (Fin 2) ℝ)} (h : Γ' ≤ Γ) (f : CuspForm Γ k) :
    CuspForm Γ' k where
  toFun := f
  slash_action_eq' A hA := f.slash_action_eq' A (h hA)
  holo' := f.holo'
  zero_at_cusps' hc := f.zero_at_cusps' (hc.mono h)

@[scoped simp] theorem coe_restrictCusp {Γ Γ' : Subgroup (GL (Fin 2) ℝ)} (h : Γ' ≤ Γ) (f : CuspForm Γ k) :
    (⇑(restrictCusp h f) : ℍ → ℂ) = f :=
  rfl

variable (N H)

def deltaH : CuspForm (ΓHℝ) 12 := restrictCusp (coe_le_SL (ΓH)) CuspForm.discriminant

@[scoped simp] theorem coe_deltaH : (⇑(deltaH N H) : ℍ → ℂ) = ModularForm.discriminant := rfl

variable {N H}

def mulDelta (f : ModularForm (ΓHℝ) k) : CuspForm (ΓHℝ) (12 + k) :=
  (deltaH N H).mulModularForm f

@[scoped simp] theorem coe_mulDelta (f : ModularForm (ΓHℝ) k) :
    (⇑(mulDelta f) : ℍ → ℂ) = (ModularForm.discriminant : ℍ → ℂ) * ⇑f := by
  rw [mulDelta, CuspForm.coe_mulModularForm, coe_deltaH]

def toG1 (F : CuspForm (ΓHℝ) k) : CuspForm (Γ₁ℝ) k := restrictCusp (coeG1_le N H) F

@[scoped simp] theorem coe_toG1 (F : CuspForm (ΓHℝ) k) : (⇑(toG1 F) : ℍ → ℂ) = F := rfl

omit N H in

theorem CuspForm_coe_sum {Γ : Subgroup (GL (Fin 2) ℝ)} {ι : Type*} (s : Finset ι)
    (F : ι → CuspForm Γ k) : (⇑(∑ i ∈ s, F i) : ℍ → ℂ) = ∑ i ∈ s, (⇑(F i) : ℍ → ℂ) :=
  map_sum (FunLike.coeAddMonoidHom (CuspForm Γ k) ℍ ℂ) F s

omit N H in

theorem ModularForm_coe_sum {Γ : Subgroup (GL (Fin 2) ℝ)} {ι : Type*} (s : Finset ι)
    (F : ι → ModularForm Γ k) : (⇑(∑ i ∈ s, F i) : ℍ → ℂ) = ∑ i ∈ s, (⇑(F i) : ℍ → ℂ) :=
  map_sum (FunLike.coeAddMonoidHom (ModularForm Γ k) ℍ ℂ) F s

end Restrict

section QExp

abbrev qL (F : ℍ → ℂ) : LaurentSeries ℂ := HahnSeries.ofPowerSeries ℤ ℂ (qExpansion 1 F)

theorem qL_mulDelta (f : ModularForm (ΓHℝ) k) :
    qL ⇑(mulDelta f) = qL (ModularForm.discriminant : ℍ → ℂ) * qL ⇑f := by
  rw [qL, coe_mulDelta, ← coe_deltaH N H,
    ModularForm.qExpansion_mul_coe one_pos (one_mem_strictPeriods_GH N H) (deltaH N H) f,
    map_mul]

theorem qL_delta_ne_zero : qL (ModularForm.discriminant : ℍ → ℂ) ≠ 0 := by
  intro h
  have h1 : qExpansion 1 (ModularForm.discriminant : ℍ → ℂ) = 0 := by
    apply HahnSeries.ofPowerSeries_injective (Γ := ℤ) (R := ℂ)
    rw [map_zero]
    exact h
  have := ModularForm.discriminant_qExpansion_coeff_one
  rw [h1, map_zero] at this
  exact zero_ne_one this

theorem coeffEmb_intSeriesC (p : PowerSeries ℤ) :
    coeffEmb ℂ (intSeriesC ℚ p) = HahnSeries.ofPowerSeries ℤ ℂ (p.map (Int.castRingHom ℂ)) := by
  ext n
  simp only [coeffEmb, intSeriesC, coeffMap_coeff, PowerSeries.coeff_coe]
  split_ifs
  · exact map_zero _
  · simp [PowerSeries.coeff_map]

theorem qL_eq_of_isIntegralQExp {F : ℍ → ℂ} {p : PowerSeries ℤ} (h : IsIntegralQExp F p) :
    HahnSeries.ofPowerSeries ℤ ℂ (p.map (Int.castRingHom ℂ)) = qL F := by
  rw [qL, ← h]

end QExp

section Trace

variable [NeZero N]

local notation "𝒬" => (↥(ΓHℝ)) ⧸ (Subgroup.subgroupOf (Γ₁ℝ) (ΓHℝ))

local instance : Fintype 𝒬 := Fintype.ofFinite _

def rep (r : ↥(ΓHℝ)) : SL(2, ℤ) := ((Subgroup.mem_map.mp r.2).choose)⁻¹

omit [NeZero N] in
theorem rep_inv_mem (r : ↥(ΓHℝ)) : (rep (N := N) (H := H) r)⁻¹ ∈ ΓH := by
  rw [rep, inv_inv]
  exact (Subgroup.mem_map.mp r.2).choose_spec.1

omit [NeZero N] in
theorem rep_mem (r : ↥(ΓHℝ)) : rep (N := N) (H := H) r ∈ ΓH := by
  simpa using Subgroup.inv_mem _ (rep_inv_mem r)

omit [NeZero N] in
theorem mapGL_rep (r : ↥(ΓHℝ)) :
    Matrix.SpecialLinearGroup.mapGL ℝ (rep (N := N) (H := H) r) = (r : GL (Fin 2) ℝ)⁻¹ := by
  rw [rep, map_inv, (Subgroup.mem_map.mp r.2).choose_spec.2]

omit [NeZero N] in

theorem quotientFunc_mk_eq (x : CuspForm (Γ₁ℝ) k) (r : ↥(ΓHℝ)) :
    quotientFunc x (⟦r⟧ : 𝒬) = (⇑x : ℍ → ℂ) ∣[k] (rep (N := N) (H := H) r) := by
  rw [quotientFunc_mk, ModularForm.SL_slash, ← mapGL_rep]
  rfl

def R (q : 𝒬) : SL(2, ℤ) := rep (N := N) (H := H) q.out

omit [NeZero N] in
theorem R_mem (q : 𝒬) : R (N := N) (H := H) q ∈ ΓH := rep_mem _

omit [NeZero N] in
theorem R_mem_Gamma0 (q : 𝒬) : R (N := N) (H := H) q ∈ Gamma0 N :=
  GammaH_le_Gamma0' N H (R_mem q)

variable (H) in

def tr (x : CuspForm (Γ₁ℝ) k) : ModularForm (ΓHℝ) k := ModularForm.trace (ΓHℝ) x

theorem coe_tr (x : CuspForm (Γ₁ℝ) k) :
    (⇑(tr H x) : ℍ → ℂ) = ∑ q : 𝒬, (⇑x : ℍ → ℂ) ∣[k] (R (N := N) (H := H) q) := by
  rw [tr, ModularForm.coe_trace]
  refine Finset.sum_congr rfl fun q _ => ?_
  conv_lhs => rw [← Quotient.out_eq q]
  exact quotientFunc_mk_eq x q.out

theorem coe_tr_sum_smul {ι : Type*} (s : Finset ι) (a : ι → ℂ) (b : ι → CuspForm (Γ₁ℝ) k) :
    (⇑(tr H (∑ i ∈ s, a i • b i)) : ℍ → ℂ) = ∑ i ∈ s, a i • (⇑(tr H (b i)) : ℍ → ℂ) := by
  rw [coe_tr]
  have hcoe : (⇑(∑ i ∈ s, a i • b i : CuspForm (Γ₁ℝ) k) : ℍ → ℂ) = ∑ i ∈ s, a i • (⇑(b i) : ℍ → ℂ) := by
    rw [CuspForm_coe_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [CuspForm.IsGLPos.coe_smul]
  simp_rw [hcoe, SlashAction.sum_slash, ModularForm.SL_smul_slash, coe_tr, Finset.smul_sum]
  exact Finset.sum_comm

theorem coe_tr_toG1 (F : CuspForm (ΓHℝ) k) :
    (⇑(tr H (toG1 F)) : ℍ → ℂ) = (Nat.card 𝒬 : ℂ) • (⇑F : ℍ → ℂ) := by
  rw [coe_tr]
  have : ∀ q : 𝒬, (⇑(toG1 F) : ℍ → ℂ) ∣[k] (R (N := N) (H := H) q) = ⇑F := by
    intro q
    rw [coe_toG1, ModularForm.SL_slash]
    exact SlashInvariantFormClass.slash_action_eq F _ (Subgroup.mem_map_of_mem _ (R_mem q))
  simp_rw [this, Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℂ,
    Nat.card_eq_fintype_card]

theorem card_Q_ne_zero : (Nat.card 𝒬 : ℂ) ≠ 0 := by
  have : 0 < Nat.card 𝒬 := Nat.card_pos
  exact_mod_cast this.ne'

theorem qExpansion_tr (x : CuspForm (Γ₁ℝ) k) :
    qExpansion 1 (⇑(tr H x) : ℍ → ℂ) =
      ∑ q : 𝒬, qExpansion 1 ((⇑x : ℍ → ℂ) ∣[k] (R (N := N) (H := H) q)) := by

  let M : 𝒬 → ModularForm (Γ₁ℝ) k := fun q => slashMF (R_mem_Gamma0 q) (x : ModularForm (Γ₁ℝ) k)
  have hM : ∀ q, (⇑(M q) : ℍ → ℂ) = (⇑x : ℍ → ℂ) ∣[k] (R (N := N) (H := H) q) := fun q => rfl
  have hsum : (⇑(tr H x) : ℍ → ℂ) = ⇑(∑ q : 𝒬, M q) := by
    rw [coe_tr, ModularForm_coe_sum]
    exact Finset.sum_congr rfl fun q _ => (hM q).symm
  rw [hsum]
  change ModularForm.qExpansionAddHom one_pos (one_mem_strictPeriods_G1 N) k (∑ q : 𝒬, M q) = _
  rw [map_sum]
  exact Finset.sum_congr rfl fun q _ => by rw [← hM q]; rfl

theorem tr_rational (x : CuspForm (Γ₁ℝ) k)
    (hx : ∀ n : ℕ, ∃ r : ℚ, (qExpansion 1 (⇑x : ℍ → ℂ)).coeff n = (r : ℂ)) (n : ℕ) :
    ∃ r : ℚ, (qExpansion 1 (⇑(tr H x) : ℍ → ℂ)).coeff n = (r : ℂ) := by
  have hq : ∀ q : 𝒬, ∃ r : ℚ,
      (qExpansion 1 ((⇑x : ℍ → ℂ) ∣[k] (R (N := N) (H := H) q))).coeff n = (r : ℂ) := fun q =>
    ModularCurve.exists_ratCast_qExpansion_slash_of_mem_Gamma0 N (x : ModularForm (Γ₁ℝ) k) hx
      (R q) (R_mem_Gamma0 q) n
  choose r hr using hq
  refine ⟨∑ q : 𝒬, r q, ?_⟩
  rw [qExpansion_tr, map_sum]
  push_cast
  exact Finset.sum_congr rfl fun q _ => hr q

theorem exists_integral_tr (x : CuspForm (Γ₁ℝ) k)
    (hx : ∀ n : ℕ, ∃ r : ℚ, (qExpansion 1 (⇑x : ℍ → ℂ)).coeff n = (r : ℂ)) :
    ∃ (D : ℤ) (p : PowerSeries ℤ), D ≠ 0 ∧ IsIntegralQExp (⇑((D : ℂ) • tr H x) : ℍ → ℂ) p := by
  obtain ⟨D, p, hD, hp⟩ := ModularCurve.exists_isIntegralQExp_smul_of_ratCast_qExpansion N
    (restrictForm (coeG1_le N H) (tr H x)) (tr_rational x hx)
  refine ⟨D, p, hD, ?_⟩
  rw [ModularForm.IsGLPos.coe_smul]
  exact hp

end Trace

section Span

variable [NeZero N]

variable (N H k) in

theorem exists_integral_span :
    ∃ (n : ℕ) (h : Fin n → ModularForm (ΓHℝ) k) (p : Fin n → PowerSeries ℤ),
      (∀ i, IsIntegralQExp (⇑(h i) : ℍ → ℂ) (p i)) ∧
      ∀ F : CuspForm (ΓHℝ) k, ∃ a : Fin n → ℂ, (⇑F : ℍ → ℂ) = ∑ i, a i • (⇑(h i) : ℍ → ℂ) := by
  classical
  obtain ⟨n, b, hb⟩ := CuspForm.exists_basis_gamma1_qCoeff_mem_range_ratCast N k
  have hbrat : ∀ i : Fin n, ∀ m : ℕ, ∃ r : ℚ,
      (qExpansion 1 (⇑(b i) : ℍ → ℂ)).coeff m = (r : ℂ) := by
    intro i m
    obtain ⟨r, hr⟩ := hb i m
    exact ⟨r, hr.symm⟩
  have key : ∀ i : Fin n, ∃ (D : ℤ) (p : PowerSeries ℤ), D ≠ 0 ∧
      IsIntegralQExp (⇑((D : ℂ) • tr H (b i)) : ℍ → ℂ) p := fun i =>
    exists_integral_tr (b i) (hbrat i)
  choose D p hD hp using key
  refine ⟨n, fun i => (D i : ℂ) • tr H (b i), p, hp, fun F => ?_⟩

  set c : ℂ := (Nat.card ((↥(ΓHℝ)) ⧸ (Subgroup.subgroupOf (Γ₁ℝ) (ΓHℝ))) : ℂ) with hc
  have hc0 : c ≠ 0 := card_Q_ne_zero
  have hrepr : toG1 F = ∑ i, (b.repr (toG1 F) i) • b i := (b.sum_repr (toG1 F)).symm
  have htr : c • (⇑F : ℍ → ℂ) = ∑ i, (b.repr (toG1 F) i) • (⇑(tr H (b i)) : ℍ → ℂ) := by
    conv_lhs => rw [← coe_tr_toG1, hrepr, coe_tr_sum_smul]
  refine ⟨fun i => c⁻¹ * (b.repr (toG1 F) i) * (D i : ℂ)⁻¹, ?_⟩
  have hDi : ∀ i, ((D i : ℂ)) ≠ 0 := fun i => Int.cast_ne_zero.2 (hD i)
  calc (⇑F : ℍ → ℂ) = c⁻¹ • (c • (⇑F : ℍ → ℂ)) := by rw [smul_smul, inv_mul_cancel₀ hc0, one_smul]
    _ = c⁻¹ • ∑ i, (b.repr (toG1 F) i) • (⇑(tr H (b i)) : ℍ → ℂ) := by rw [htr]
    _ = ∑ i, (c⁻¹ * (b.repr (toG1 F) i) * (D i : ℂ)⁻¹) • (⇑((D i : ℂ) • tr H (b i)) : ℍ → ℂ) := by
        rw [Finset.smul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [ModularForm.IsGLPos.coe_smul, smul_smul, smul_smul, mul_assoc, inv_mul_cancel₀ (hDi i),
          mul_one]

omit [NeZero N] in

theorem qL_eq_sum {n : ℕ} (h : Fin n → ModularForm (ΓHℝ) k) (p : Fin n → PowerSeries ℤ)
    (hp : ∀ i, IsIntegralQExp (⇑(h i) : ℍ → ℂ) (p i)) (F : CuspForm (ΓHℝ) k) (a : Fin n → ℂ)
    (hF : (⇑F : ℍ → ℂ) = ∑ i, a i • (⇑(h i) : ℍ → ℂ)) :
    qL ⇑F = ∑ i, algebraMap ℂ (LaurentSeries ℂ) (a i) *
      HahnSeries.ofPowerSeries ℤ ℂ ((p i).map (Int.castRingHom ℂ)) := by
  classical

  have hS : (⇑F : ℍ → ℂ) = ⇑(∑ i, a i • h i : ModularForm (ΓHℝ) k) := by
    rw [hF, ModularForm_coe_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [ModularForm.IsGLPos.coe_smul]
  have hq : qExpansion 1 (⇑F : ℍ → ℂ) = ∑ i, a i • qExpansion 1 (⇑(h i) : ℍ → ℂ) := by
    rw [hS]
    change ModularForm.qExpansionAddHom one_pos (one_mem_strictPeriods_GH N H) k
      (∑ i, a i • h i) = _
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    change qExpansion 1 (⇑(a i • h i) : ℍ → ℂ) = _
    rw [ModularForm.IsGLPos.coe_smul]
    exact ModularForm.qExpansion_smul one_pos (one_mem_strictPeriods_GH N H) (a i) (h i)
  rw [qL, hq, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [PowerSeries.smul_eq_C_mul, map_mul, PowerSeries.C_eq_algebraMap, ← HahnSeries.algebraMap_apply',
    (hp i)]

end Span

section Main

variable [NeZero N]

omit [NeZero N] in

theorem ratio_mem {K : ℤ} (hi hj : ModularForm (ΓHℝ) K) {pi pj : PowerSeries ℤ}
    (hpi : IsIntegralQExp (⇑hi : ℍ → ℂ) pi) (hpj : IsIntegralQExp (⇑hj : ℍ → ℂ) pj)
    (hj0 : HahnSeries.ofPowerSeries ℤ ℂ (pj.map (Int.castRingHom ℂ)) ≠ 0) :
    HahnSeries.ofPowerSeries ℤ ℂ (pi.map (Int.castRingHom ℂ)) /
        HahnSeries.ofPowerSeries ℤ ℂ (pj.map (Int.castRingHom ℂ)) ∈
      laurentBaseChange ℂ (xHFunctionField N H) := by
  have hj0' : intSeriesC ℚ pj ≠ 0 := by
    intro h0
    apply hj0
    rw [← coeffEmb_intSeriesC, h0, map_zero]
  have hmem : intSeriesC ℚ pi / intSeriesC ℚ pj ∈ xHFunctionField N H :=
    div_mem_qExpFunctionFieldC hi hj hpi hpj hj0'
  have := coeffEmb_mem_laurentBaseChange ℂ hmem
  rwa [map_div₀, coeffEmb_intSeriesC, coeffEmb_intSeriesC] at this

theorem main (f g : ModularForm (ΓHℝ) k) :
    qL ⇑f / qL ⇑g ∈ laurentBaseChange ℂ (xHFunctionField N H) := by
  classical
  set 𝔽 := laurentBaseChange ℂ (xHFunctionField N H)

  have hratio : qL ⇑f / qL ⇑g = qL ⇑(mulDelta f) / qL ⇑(mulDelta g) := by
    rw [qL_mulDelta, qL_mulDelta, mul_div_mul_left _ _ qL_delta_ne_zero]
  rw [hratio]

  obtain ⟨n, h, p, hp, hspan⟩ := exists_integral_span N H (12 + k)
  obtain ⟨a, ha⟩ := hspan (mulDelta f)
  obtain ⟨c, hc⟩ := hspan (mulDelta g)
  set P : Fin n → LaurentSeries ℂ := fun i =>
    HahnSeries.ofPowerSeries ℤ ℂ ((p i).map (Int.castRingHom ℂ)) with hP
  have hFa : qL ⇑(mulDelta f) = ∑ i, algebraMap ℂ (LaurentSeries ℂ) (a i) * P i :=
    qL_eq_sum h p hp (mulDelta f) a ha
  have hGc : qL ⇑(mulDelta g) = ∑ i, algebraMap ℂ (LaurentSeries ℂ) (c i) * P i :=
    qL_eq_sum h p hp (mulDelta g) c hc
  by_cases hex : ∃ j, P j ≠ 0
  · obtain ⟨j, hj⟩ := hex
    have hmem : ∀ i, P i / P j ∈ 𝔽 := fun i => ratio_mem (h i) (h j) (hp i) (hp j) hj
    have hnum : qL ⇑(mulDelta f) / P j ∈ 𝔽 := by
      rw [hFa, Finset.sum_div]
      refine IntermediateField.sum_mem 𝔽 fun i _ => ?_
      rw [mul_div_assoc]
      exact mul_mem (IntermediateField.algebraMap_mem 𝔽 (a i)) (hmem i)
    have hden : qL ⇑(mulDelta g) / P j ∈ 𝔽 := by
      rw [hGc, Finset.sum_div]
      refine IntermediateField.sum_mem 𝔽 fun i _ => ?_
      rw [mul_div_assoc]
      exact mul_mem (IntermediateField.algebraMap_mem 𝔽 (c i)) (hmem i)
    have := div_mem hnum hden
    rwa [div_div_div_cancel_right₀ hj] at this
  · push Not at hex
    have hG0 : qL ⇑(mulDelta g) = 0 := by
      rw [hGc]
      exact Finset.sum_eq_zero fun i _ => by rw [hex i, mul_zero]
    rw [hG0, div_zero]
    exact zero_mem 𝔽

end Main

end XHRationalStructure
p2m_reactivate "P2MW.S_ModularCurve_qExpansion_div_mem_laurentBaseChange_xHFunctionField.XHRationalStructure"

end
p2m_reactivate "P2MW.S_ModularCurve_qExpansion_div_mem_laurentBaseChange_xHFunctionField.XHRationalStructure"

set_option linter.unusedVariables false in
theorem solution (N : ℕ) [NeZero N]
    (H : Subgroup (ZMod N)ˣ) {k : ℤ}
    (f g : ModularForm (CohCarrier.GammaH N H : Subgroup (GL (Fin 2) ℝ)) k) (hg : g ≠ 0) :
    HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑f) /
        HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑g) ∈
      ModularCurve.laurentBaseChange ℂ (ModularCurve.xHFunctionField N H) :=
  XHRationalStructure.main f g

end S_ModularCurve_qExpansion_div_mem_laurentBaseChange_xHFunctionField
end P2MW
export P2MW.S_ModularCurve_qExpansion_div_mem_laurentBaseChange_xHFunctionField (solution)
