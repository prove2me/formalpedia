-- Prove2me | solution 1 for ModPForms.eq_zero_of_mem_modPCusp_of_expand_mem_modPCusp
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/8bd4ce52-bda1-5474-a873-6c9bf305be64

import Definitions.Def_CuspForm_ModPForms
import Definitions.Def_CuspForm_IntegralStructure
import Definitions.Def_ModularForm_HeckeOperatorForms
import Theorems.Thm_ModularFormClass_qCoeff_heckeT
import Theorems.Thm_CuspForm_intLattice_fg
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModPForms_eq_zero_of_mem_modPCusp_of_expand_mem_modPCusp

set_option autoImplicit false

noncomputable section

open CuspForm
open scoped ModularForm

namespace WLDesc

section Coeff

variable {M : ℕ} {k : ℤ}

private theorem one_mem_strictPeriods_Gamma0 (M : ℕ) :
    (1 : ℝ) ∈ (CongruenceSubgroup.Gamma0 M : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
  rw [CongruenceSubgroup.strictPeriods_Gamma0]
  exact AddSubgroup.mem_zmultiples _

private theorem qCoeff_add' (f g : CuspForm (CongruenceSubgroup.Gamma0 M) k) (n : ℕ) :
    ModularFormClass.qCoeff (⇑(f + g)) n = ModularFormClass.qCoeff f n + ModularFormClass.qCoeff g n := by
  unfold ModularFormClass.qCoeff
  rw [CuspForm.coe_add, ModularForm.qExpansion_add one_pos (one_mem_strictPeriods_Gamma0 M) f g,
    map_add]

private theorem qCoeff_zero' (n : ℕ) :
    ModularFormClass.qCoeff (⇑(0 : CuspForm (CongruenceSubgroup.Gamma0 M) k)) n = 0 := by
  unfold ModularFormClass.qCoeff
  rw [CuspForm.coe_zero, UpperHalfPlane.qExpansion_zero, map_zero]

private def qCoeffAddHom (n : ℕ) : CuspForm (CongruenceSubgroup.Gamma0 M) k →+ ℂ where
  toFun f := ModularFormClass.qCoeff f n
  map_zero' := qCoeff_zero' n
  map_add' f g := qCoeff_add' f g n

private theorem qCoeffAddHom_apply (n : ℕ) (f : CuspForm (CongruenceSubgroup.Gamma0 M) k) :
    qCoeffAddHom n f = ModularFormClass.qCoeff f n := rfl

private theorem qCoeff_zsmul' (m : ℤ) (f : CuspForm (CongruenceSubgroup.Gamma0 M) k) (n : ℕ) :
    ModularFormClass.qCoeff (⇑(m • f)) n = m * ModularFormClass.qCoeff f n := by
  show qCoeffAddHom n (m • f) = m * qCoeffAddHom n f
  rw [map_zsmul, zsmul_eq_mul]

private theorem qCoeff_sum' {ι : Type} (s : Finset ι) (g : ι → CuspForm (CongruenceSubgroup.Gamma0 M) k) (n : ℕ) :
    ModularFormClass.qCoeff (⇑(∑ i ∈ s, g i)) n = ∑ i ∈ s, ModularFormClass.qCoeff (g i) n := by
  show qCoeffAddHom n (∑ i ∈ s, g i) = ∑ i ∈ s, qCoeffAddHom n (g i)
  rw [map_sum]

private theorem qCoeff_heckeTLin' {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M)
    (f : CuspForm (CongruenceSubgroup.Gamma0 M) k) (n : ℕ) :
    ModularFormClass.qCoeff (heckeTLin k hℓ hℓM f) n =
      ModularForm.coeffHeckeT k ℓ (ModularFormClass.qCoeff f) n := by
  rw [coe_heckeTLin_apply]
  exact ModularFormClass.qCoeff_heckeT f (one_mem_strictPeriods_Gamma0 M) hℓ.ne_zero n

private theorem exists_int_qCoeff_of_mem_intLattice {f : CuspForm (CongruenceSubgroup.Gamma0 M) k}
    (hf : f ∈ intLattice M k) (n : ℕ) : ∃ m : ℤ, ModularFormClass.qCoeff f n = (m : ℂ) := by
  induction hf using Submodule.span_induction with
  | mem x hx => exact hx n
  | zero => exact ⟨0, by rw [qCoeff_zero', Int.cast_zero]⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    exact ⟨a + b, by rw [qCoeff_add', ha, hb, Int.cast_add]⟩
  | smul a x _ hx =>
    obtain ⟨b, hb⟩ := hx
    exact ⟨a * b, by rw [qCoeff_zsmul', hb, Int.cast_mul]⟩

private theorem qCoeff_index_zero (f : CuspForm (CongruenceSubgroup.Gamma0 M) k) : ModularFormClass.qCoeff f 0 = 0 :=
  CuspFormClass.qExpansion_coeff_zero f one_pos (one_mem_strictPeriods_Gamma0 M)

private theorem cuspForm_coe_eq_zero_of_nonpos_weight [NeZero M] {w : ℤ} (hw : w ≤ 0)
    (G : CuspForm (CongruenceSubgroup.Gamma0 M) w) : ⇑G = 0 := by
  let Gm : ModularForm (CongruenceSubgroup.Gamma0 M) w :=
    { toSlashInvariantForm := G.toSlashInvariantForm
      holo' := G.holo'
      bdd_at_cusps' := fun hc g hg =>
        Filter.ZeroAtFilter.boundedAtFilter (G.zero_at_cusps' hc g hg) }
  rcases hw.lt_or_eq with hlt | heq
  · have h0 := ModularForm.isZero_of_neg_weight hlt Gm
    have hGm : ⇑G = ⇑Gm := rfl
    rw [hGm, h0]
    rfl
  · subst heq
    obtain ⟨c, hc⟩ := ModularForm.eq_const_of_weight_zero Gm
    have hinf : IsCusp OnePoint.infty
        (Subgroup.map (Matrix.SpecialLinearGroup.mapGL ℝ) (CongruenceSubgroup.Gamma0 M)) :=
      Subgroup.isCusp_of_mem_strictPeriods one_pos (one_mem_strictPeriods_Gamma0 M)
    have hz : UpperHalfPlane.IsZeroAtImInfty (⇑G ∣[(0 : ℤ)] (1 : Matrix.GeneralLinearGroup (Fin 2) ℝ)) :=
      G.zero_at_cusps' hinf 1 (by simp)
    rw [SlashAction.slash_one] at hz
    have hGm : ⇑G = ⇑Gm := rfl
    rw [hGm, hc] at hz ⊢
    have hz' : Filter.Tendsto (Function.const UpperHalfPlane c) UpperHalfPlane.atImInfty (nhds 0) := hz
    have hc0 : c = 0 := (tendsto_nhds_unique hz' tendsto_const_nhds).symm
    rw [hc0]
    rfl

end Coeff

section PS

variable {F : Type} [Field F]

private def expandV (p : ℕ) (φ : PowerSeries F) : PowerSeries F :=
  PowerSeries.mk fun n => if p ∣ n then PowerSeries.coeff (n / p) φ else 0

private theorem coeff_expandV (p : ℕ) (φ : PowerSeries F) (n : ℕ) :
    PowerSeries.coeff n (expandV p φ) = if p ∣ n then PowerSeries.coeff (n / p) φ else 0 :=
  PowerSeries.coeff_mk _ _

private theorem coeff_mul_expandV {p : ℕ} (hp : 0 < p) (φ : PowerSeries F) (n : ℕ) :
    PowerSeries.coeff (n * p) (expandV p φ) = PowerSeries.coeff n φ := by
  rw [coeff_expandV, if_pos (Dvd.intro_left n rfl), Nat.mul_div_cancel n hp]

private theorem coeff_iterate_expandV (p : ℕ) (φ : PowerSeries F) (j m : ℕ) :
    PowerSeries.coeff m ((expandV p)^[j] φ) = if p ^ j ∣ m then PowerSeries.coeff (m / p ^ j) φ else 0 := by
  induction j generalizing m with
  | zero => simp
  | succ j ih =>
    rw [Function.iterate_succ_apply', coeff_expandV]
    by_cases hpm : p ∣ m
    · rw [if_pos hpm, ih, pow_succ', ← Nat.div_div_eq_div_mul]
      by_cases hj : p ^ j ∣ m / p
      · rw [if_pos hj, if_pos ((Nat.dvd_div_iff_mul_dvd hpm).mp hj)]
      · rw [if_neg hj, if_neg (fun h => hj ((Nat.dvd_div_iff_mul_dvd hpm).mpr h))]
    · rw [if_neg hpm, if_neg (fun h => hpm ((dvd_pow_self p (Nat.succ_ne_zero j)).trans h))]

private theorem heckePS_add (k : ℤ) (p : ℕ) (φ ψ : PowerSeries F) :
    ModPForms.heckePS k p (φ + ψ) = ModPForms.heckePS k p φ + ModPForms.heckePS k p ψ := by
  ext n
  simp only [ModPForms.heckePS, PowerSeries.coeff_mk, map_add]
  split_ifs <;> ring

private theorem heckePS_smul (k : ℤ) (p : ℕ) (c : F) (φ : PowerSeries F) :
    ModPForms.heckePS k p (c • φ) = c • ModPForms.heckePS k p φ := by
  ext n
  simp only [ModPForms.heckePS, PowerSeries.coeff_mk, map_smul, smul_eq_mul]
  split_ifs <;> ring

private theorem heckePS_zero (k : ℤ) (p : ℕ) : ModPForms.heckePS k p (0 : PowerSeries F) = 0 := by
  ext n
  simp only [ModPForms.heckePS, PowerSeries.coeff_mk, map_zero, mul_zero, ite_self, add_zero]

private theorem heckePS_expandV (k : ℤ) {p : ℕ} (hp : 0 < p) (φ : PowerSeries F) :
    ModPForms.heckePS k p (expandV p φ) = φ + ((p : F) ^ (k - 1)) • expandV p (expandV p φ) := by
  ext n
  simp only [ModPForms.heckePS, PowerSeries.coeff_mk, map_add, map_smul, smul_eq_mul]
  rw [coeff_mul_expandV hp, coeff_expandV p (expandV p φ) n]
  split_ifs <;> ring

end PS

section Span

variable (p : ℕ) (hp : p.Prime) (N : ℕ) [NeZero N] (hpN : ¬ p ∣ N) (k : ℤ) (F : Type) [Field F]

omit [NeZero N] in
include hp hpN in
private theorem heckePS_mem_modPCusp (hk : 1 ≤ k) {φ : PowerSeries F} (hφ : φ ∈ ModPForms.modPCusp N k F) :
    ModPForms.heckePS k p φ ∈ ModPForms.modPCusp N k F := by
  induction hφ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, a, hf, rfl⟩ := hx
    obtain ⟨e, he⟩ : ∃ e : ℕ, k - 1 = (e : ℤ) := ⟨(k - 1).toNat, (Int.toNat_of_nonneg (by omega)).symm⟩
    let b : ℕ → ℤ := fun n => a (n * p) + if p ∣ n then (p : ℤ) ^ e * a (n / p) else 0
    refine Submodule.subset_span ⟨heckeTLin k hp hpN f, b, fun n => ?_, ?_⟩
    · rw [qCoeff_heckeTLin', ModularForm.coeffHeckeT_apply, hf]
      by_cases hdiv : p ∣ n
      · simp only [b, if_pos hdiv, hf, he, zpow_natCast]
        push_cast
        ring
      · simp only [b, if_neg hdiv, add_zero]
    · ext n
      simp only [ModPForms.heckePS, PowerSeries.coeff_mk, b, he, zpow_natCast]
      by_cases hdiv : p ∣ n
      · rw [if_pos hdiv, if_pos hdiv]
        push_cast
        ring
      · rw [if_neg hdiv, if_neg hdiv]
        push_cast
        ring
  | zero => rw [heckePS_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [heckePS_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [heckePS_smul]; exact Submodule.smul_mem _ c hx

omit [NeZero N] in
private theorem coeff_zero_of_mem_modPCusp {φ : PowerSeries F} (hφ : φ ∈ ModPForms.modPCusp N k F) :
    PowerSeries.coeff 0 φ = 0 := by
  induction hφ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, a, hf, rfl⟩ := hx
    have h0 : ((a 0 : ℤ) : ℂ) = 0 := by rw [← hf 0, qCoeff_index_zero]
    rw [PowerSeries.coeff_mk, show a 0 = 0 by exact_mod_cast h0, Int.cast_zero]
  | zero => exact map_zero _
  | add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]
  | smul c x _ hx => rw [map_smul, hx, smul_zero]

private theorem eq_zero_of_mem_modPCusp_of_nonpos (hk : k ≤ 0) {φ : PowerSeries F} (hφ : φ ∈ ModPForms.modPCusp N k F) :
    φ = 0 := by
  induction hφ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, a, hf, rfl⟩ := hx
    have hf0 : (⇑f : UpperHalfPlane → ℂ) = 0 := cuspForm_coe_eq_zero_of_nonpos_weight hk f
    ext n
    have h0 : ((a n : ℤ) : ℂ) = 0 := by
      rw [← hf n, hf0]
      show PowerSeries.coeff n (UpperHalfPlane.qExpansion 1 (0 : UpperHalfPlane → ℂ)) = 0
      rw [UpperHalfPlane.qExpansion_zero, map_zero]
    rw [PowerSeries.coeff_mk, show a n = 0 by exact_mod_cast h0, Int.cast_zero, map_zero]
  | zero => rfl
  | add x y _ _ hx hy => rw [hx, hy, add_zero]
  | smul c x _ hx => rw [hx, smul_zero]

open Classical in

private def icoef (g : CuspForm (CongruenceSubgroup.Gamma0 N) k) (n : ℕ) : ℤ :=
  if h : ∃ m : ℤ, ModularFormClass.qCoeff g n = (m : ℂ) then h.choose else 0

omit [NeZero N] in
private theorem icoef_spec {g : CuspForm (CongruenceSubgroup.Gamma0 N) k} (hg : g ∈ intLattice N k) (n : ℕ) :
    ModularFormClass.qCoeff g n = (icoef N k g n : ℂ) := by
  have h := exists_int_qCoeff_of_mem_intLattice hg n
  rw [icoef, dif_pos h]
  exact h.choose_spec

private theorem finiteDimensional_modPCusp : FiniteDimensional F (ModPForms.modPCusp N k F) := by
  classical
  obtain ⟨G, hG⟩ := CuspForm.intLattice_fg N k
  let red : CuspForm (CongruenceSubgroup.Gamma0 N) k → PowerSeries F :=
    fun g => PowerSeries.mk fun n => ((icoef N k g n : ℤ) : F)
  let W : Submodule F (PowerSeries F) := Submodule.span F (red '' (G : Set _))
  haveI : FiniteDimensional F W := FiniteDimensional.span_of_finite F ((G.finite_toSet).image red)
  refine Submodule.finiteDimensional_of_le (Submodule.span_le.mpr ?_ : ModPForms.modPCusp N k F ≤ W)
  rintro φ ⟨f, a, hf, rfl⟩
  have hfL : f ∈ intLattice N k := Submodule.subset_span fun n => ⟨a n, hf n⟩
  rw [← hG, Submodule.mem_span_finset] at hfL
  obtain ⟨c, -, hc⟩ := hfL
  have hGL : ∀ g ∈ G, g ∈ intLattice N k := fun g hg => by
    rw [← hG]; exact Submodule.subset_span hg
  have ha : ∀ n, a n = ∑ g ∈ G, c g * icoef N k g n := by
    intro n
    have h1 : ((a n : ℤ) : ℂ) = ((∑ g ∈ G, c g * icoef N k g n : ℤ) : ℂ) := by
      rw [← hf n, ← hc, qCoeff_sum']
      push_cast
      refine Finset.sum_congr rfl fun g hg => ?_
      rw [← CuspForm.coe_smul, qCoeff_zsmul', icoef_spec N k (hGL g hg)]
    exact_mod_cast h1
  have hφ : (PowerSeries.mk fun n => ((a n : ℤ) : F)) = ∑ g ∈ G, (c g : F) • red g := by
    ext n
    simp only [PowerSeries.coeff_mk, map_sum, map_smul, smul_eq_mul, red, ha]
    push_cast
    rfl
  rw [hφ]
  exact W.sum_mem fun g hg => W.smul_mem _ (Submodule.subset_span ⟨g, hg, rfl⟩)

end Span

private theorem desc_main (p : ℕ) (hp : p.Prime) (N : ℕ) (hpN : ¬ p ∣ N) (k : ℤ)
    (F : Type) [Field F] (hpF : (p : F) ≠ 0)
    (ψ : PowerSeries F) (hψ : ψ ∈ ModPForms.modPCusp N k F)
    (hV : (PowerSeries.mk fun n => if p ∣ n then PowerSeries.coeff (n / p) ψ else 0) ∈ ModPForms.modPCusp N k F) :
    ψ = 0 := by
  classical
  haveI : NeZero N := ⟨fun h => hpN (h ▸ dvd_zero p)⟩
  rcases le_or_gt k 0 with hk | hk
  · exact eq_zero_of_mem_modPCusp_of_nonpos N k F hk hψ
  have hk1 : 1 ≤ k := by omega
  change expandV p ψ ∈ ModPForms.modPCusp N k F at hV
  by_contra hne
  set S := ModPForms.modPCusp N k F with hS
  have hc0 : ((p : F) ^ (k - 1)) ≠ 0 := zpow_ne_zero _ hpF

  have hiter : ∀ j : ℕ, (expandV p)^[j] ψ ∈ S ∧ (expandV p)^[j + 1] ψ ∈ S := by
    intro j
    induction j with
    | zero => exact ⟨hψ, hV⟩
    | succ j ih =>
      refine ⟨ih.2, ?_⟩
      have key := heckePS_expandV (F := F) k hp.pos ((expandV p)^[j] ψ)
      rw [← Function.iterate_succ_apply' (expandV p) j ψ] at key
      have hT : ModPForms.heckePS k p ((expandV p)^[j + 1] ψ) ∈ S := heckePS_mem_modPCusp p hp N hpN k F hk1 ih.2
      have hVV : expandV p ((expandV p)^[j + 1] ψ)
          = ((p : F) ^ (k - 1))⁻¹ • (ModPForms.heckePS k p ((expandV p)^[j + 1] ψ) - (expandV p)^[j] ψ) := by
        rw [key, add_sub_cancel_left, smul_smul, inv_mul_cancel₀ hc0, one_smul]
      rw [Function.iterate_succ_apply', hVV]
      exact S.smul_mem _ (S.sub_mem hT ih.1)

  have hex : ∃ n, PowerSeries.coeff n ψ ≠ 0 := by
    by_contra h
    push Not at h
    exact hne (PowerSeries.ext fun n => by rw [h n, map_zero])
  obtain ⟨n₀, hn₀, hmin⟩ : ∃ n₀, PowerSeries.coeff n₀ ψ ≠ 0 ∧ ∀ m < n₀, PowerSeries.coeff m ψ = 0 :=
    ⟨Nat.find hex, Nat.find_spec hex, fun m hm => not_not.mp (Nat.find_min hex hm)⟩
  have hn₀pos : 0 < n₀ := Nat.pos_of_ne_zero fun h0 => hn₀ (by rw [h0]; exact coeff_zero_of_mem_modPCusp N k F hψ)

  let v : ℕ → S := fun j => ⟨(expandV p)^[j] ψ, (hiter j).1⟩
  have hli : LinearIndependent F v := by
    rw [linearIndependent_iff']
    intro s g hsum i hi
    by_contra hgi
    let t := s.filter fun j => g j ≠ 0
    have hit : i ∈ t := Finset.mem_filter.mpr ⟨hi, hgi⟩
    have ht : t.Nonempty := ⟨i, hit⟩
    have hi₀t : t.min' ht ∈ t := t.min'_mem ht
    have hi₀s : t.min' ht ∈ s := (Finset.mem_filter.mp hi₀t).1
    have hgi₀ : g (t.min' ht) ≠ 0 := (Finset.mem_filter.mp hi₀t).2
    have hmin' : ∀ j ∈ s, g j ≠ 0 → t.min' ht ≤ j := fun j hj hgj => t.min'_le j (Finset.mem_filter.mpr ⟨hj, hgj⟩)
    set i₀ := t.min' ht with hi₀
    have hsum' : ∑ j ∈ s, g j • (expandV p)^[j] ψ = 0 := by
      have h := congrArg (fun x : S => (x : PowerSeries F)) hsum
      simpa [v] using h
    have hcoef := congrArg (PowerSeries.coeff (n₀ * p ^ i₀)) hsum'
    rw [map_sum, map_zero, Finset.sum_eq_single i₀] at hcoef
    · rw [map_smul, coeff_iterate_expandV p, if_pos (Dvd.intro_left n₀ rfl),
        Nat.mul_div_cancel n₀ (pow_pos hp.pos i₀), smul_eq_mul] at hcoef
      exact hgi₀ ((mul_eq_zero.mp hcoef).resolve_right hn₀)
    · intro j hj hji
      by_cases hgj : g j = 0
      · rw [hgj, zero_smul, map_zero]
      have hlt : i₀ < j := lt_of_le_of_ne (hmin' j hj hgj) (Ne.symm hji)
      rw [map_smul, coeff_iterate_expandV p]
      split_ifs with hdvd
      · obtain ⟨c, hc⟩ := hdvd
        have hpj : p ^ j = p ^ i₀ * p ^ (j - i₀) := by rw [← pow_add, Nat.add_sub_cancel' hlt.le]
        have hn₀c : n₀ = p ^ (j - i₀) * c := by
          apply Nat.eq_of_mul_eq_mul_left (pow_pos hp.pos i₀)
          rw [mul_comm (p ^ i₀) n₀, hc, hpj, mul_assoc]
        have h2 : 2 ≤ p ^ (j - i₀) := by
          have := Nat.one_lt_pow (Nat.sub_ne_zero_of_lt hlt) hp.one_lt
          omega
        have hclt : c < n₀ := by
          rcases Nat.eq_zero_or_pos c with hc0 | hcpos
          · omega
          · nlinarith
        rw [hc, Nat.mul_div_cancel_left c (pow_pos hp.pos j), hmin c hclt, smul_zero]
      · rw [smul_zero]
    · exact fun h => absurd hi₀s h
  haveI : FiniteDimensional F S := finiteDimensional_modPCusp N k F
  exact Module.Finite.not_linearIndependent_of_infinite v hli

end WLDesc

theorem solution
    (p : ℕ) (hp : p.Prime) (N : ℕ) (hpN : ¬ p ∣ N) (k : ℤ)
    (F : Type) [Field F] (hpF : (p : F) ≠ 0)
    (ψ : PowerSeries F) (hψ : ψ ∈ ModPForms.modPCusp N k F)
    (hV : (PowerSeries.mk fun n => if p ∣ n then PowerSeries.coeff (n / p) ψ else 0) ∈ ModPForms.modPCusp N k F) :
    ψ = 0 :=
  WLDesc.desc_main p hp N hpN k F hpF ψ hψ hV

end

end S_ModPForms_eq_zero_of_mem_modPCusp_of_expand_mem_modPCusp
end P2MW
export P2MW.S_ModPForms_eq_zero_of_mem_modPCusp_of_expand_mem_modPCusp (solution)
