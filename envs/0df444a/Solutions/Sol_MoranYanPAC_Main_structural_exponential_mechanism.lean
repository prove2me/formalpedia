-- Prove2me | solution 1 for MoranYanPAC.Main.structural_exponential_mechanism
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-20T11:33:05.216473+00:00
-- url     : https://prove2.me/submissions/2d3d2231-3cc5-4a66-9bdb-f3444fb3d35b

import Mathlib
import Definitions.Def_PrivLittlestone_IsInsDelNeighbor
import Definitions.Def_MoranYanPAC_Main_PrivateLaw
import Definitions.Def_MoranYanPAC_Main_StructuralMechanism

section
set_option autoImplicit false

namespace MoranYanPAC.Dev.Priv

open Finset

variable {Y : Type*} [DecidableEq Y]

theorem priv_real (oS oT : Finset Y) (wS wT : Y → ℝ) (ε δ : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hδ : 0 < δ) (hδ1 : δ < 1)
    (hSpos : ∀ h ∈ oS, 0 < wS h) (hTpos : ∀ h ∈ oT, 0 < wT h)
    (hSne : oS.Nonempty) (hTne : oT.Nonempty)
    (h1 : ∀ h ∈ oS ∩ oT, wS h ≤ Real.exp (ε / 2) * wT h)
    (h1' : ∀ h ∈ oS ∩ oT, wT h ≤ Real.exp (ε / 2) * wS h)
    (h2 : ∑ g ∈ oS \ oT, wS g ≤ δ / 4 * ∑ h ∈ oT, wT h)
    (h2' : ∑ g ∈ oT \ oS, wT g ≤ δ / 4 * ∑ h ∈ oS, wS h)
    (E : Set Y) [DecidablePred (· ∈ E)] :
    (∑ h ∈ oS.filter (· ∈ E), wS h) / (∑ h ∈ oS, wS h) ≤
      Real.exp ε * ((∑ h ∈ oT.filter (· ∈ E), wT h) / (∑ h ∈ oT, wT h)) + δ := by
  set ZS := ∑ h ∈ oS, wS h with hZS
  set ZT := ∑ h ∈ oT, wT h with hZT
  have hZSpos : 0 < ZS := Finset.sum_pos hSpos hSne
  have hZTpos : 0 < ZT := Finset.sum_pos hTpos hTne
  set x := Real.exp (ε / 2) with hx
  have hx1 : 1 ≤ x := Real.one_le_exp (by linarith)
  have hx2 : x < 17 / 10 := by
    have h0 : Real.exp (ε / 2) ≤ Real.exp (1 / 2) := Real.exp_le_exp.2 (by linarith)
    have hsq : Real.exp (1 / 2) * Real.exp (1 / 2) = Real.exp 1 := by rw [← Real.exp_add]; norm_num
    have h3 := Real.exp_one_lt_d9
    have h4 := Real.exp_pos (1 / 2)
    nlinarith
  have hxx : Real.exp ε = x * x := by rw [hx, ← Real.exp_add]; ring_nf
  -- split sums
  have hsplitS : ∀ (P : Y → Prop) [DecidablePred P], ∑ h ∈ oS.filter P, wS h =
      ∑ h ∈ (oS ∩ oT).filter P, wS h + ∑ h ∈ (oS \ oT).filter P, wS h := by
    intro P _
    rw [← Finset.sum_union]
    · congr 1; ext h; simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]; tauto
    · refine Finset.disjoint_left.2 fun h h1 h2 => ?_
      simp only [Finset.mem_filter, Finset.mem_inter, Finset.mem_sdiff] at h1 h2; tauto
  have hsplitT : ∀ (P : Y → Prop) [DecidablePred P], ∑ h ∈ oT.filter P, wT h =
      ∑ h ∈ (oS ∩ oT).filter P, wT h + ∑ h ∈ (oT \ oS).filter P, wT h := by
    intro P _
    rw [← Finset.sum_union]
    · congr 1; ext h; simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]; tauto
    · refine Finset.disjoint_left.2 fun h h1 h2 => ?_
      simp only [Finset.mem_filter, Finset.mem_inter, Finset.mem_sdiff] at h1 h2; tauto
  have hsubS : ∑ h ∈ (oS \ oT).filter (· ∈ E), wS h ≤ ∑ g ∈ oS \ oT, wS g :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun h hh _ => (hSpos h (Finset.mem_sdiff.1 hh).1).le)
  have hsubT : ∑ h ∈ (oT \ oS).filter (· ∈ E), wT h ≤ ∑ g ∈ oT \ oS, wT g :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun h hh _ => (hTpos h (Finset.mem_sdiff.1 hh).1).le)
  have hI_S : ∑ h ∈ oS ∩ oT, wS h ≤ ZS :=
    Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_left
      (fun h hh _ => (hSpos h hh).le)
  -- Z_T bound
  have hZTle : ZT ≤ (x + δ / 4) * ZS := by
    have e1 : ZT = ∑ h ∈ oS ∩ oT, wT h + ∑ h ∈ oT \ oS, wT h := by
      have := hsplitT (fun _ => True)
      simpa using this
    have e2 : ∑ h ∈ oS ∩ oT, wT h ≤ x * ∑ h ∈ oS ∩ oT, wS h := by
      rw [Finset.mul_sum]; exact Finset.sum_le_sum h1'
    nlinarith
  -- numerator bound
  have hnum : ∑ h ∈ oS.filter (· ∈ E), wS h ≤ x * ∑ h ∈ oT.filter (· ∈ E), wT h + δ / 4 * ZT := by
    rw [hsplitS]
    have e2 : ∑ h ∈ (oS ∩ oT).filter (· ∈ E), wS h ≤ x * ∑ h ∈ (oS ∩ oT).filter (· ∈ E), wT h := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun h hh => h1 h ?_
      exact (Finset.mem_filter.1 hh).1
    have e3 : ∑ h ∈ (oS ∩ oT).filter (· ∈ E), wT h ≤ ∑ h ∈ oT.filter (· ∈ E), wT h :=
      Finset.sum_le_sum_of_subset_of_nonneg
        (fun h hh => Finset.mem_filter.2 ⟨(Finset.mem_inter.1 (Finset.mem_filter.1 hh).1).2,
          (Finset.mem_filter.1 hh).2⟩)
        (fun h hh _ => (hTpos h (Finset.mem_filter.1 hh).1).le)
    nlinarith
  set NT := ∑ h ∈ oT.filter (· ∈ E), wT h with hNT
  have hNTle : NT ≤ ZT := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    (fun h hh _ => (hTpos h hh).le)
  have hNTnn : 0 ≤ NT := Finset.sum_nonneg fun h hh => (hTpos h (Finset.mem_filter.1 hh).1).le
  rw [div_le_iff₀ hZSpos]
  have hPT : NT / ZT ≤ 1 := (div_le_one hZTpos).2 hNTle
  have hNTe : NT = (NT / ZT) * ZT := by field_simp
  set PT := NT / ZT with hPTdef
  have hPTnn : 0 ≤ PT := div_nonneg hNTnn hZTpos.le
  rw [hxx]
  -- goal: numerator ≤ (x*x*PT + δ) * ZS
  have hc : ZT ≤ (x + δ / 4) * ZS := hZTle
  have : x * NT + δ / 4 * ZT = (x * PT + δ / 4) * ZT := by rw [hNTe]; ring
  have h5 : (x * PT + δ / 4) * ZT ≤ (x * PT + δ / 4) * ((x + δ / 4) * ZS) :=
    mul_le_mul_of_nonneg_left hc (by positivity)
  have h6 : (x * PT + δ / 4) * ((x + δ / 4) * ZS) ≤ (x * x * PT + δ) * ZS := by
    have : (x * PT + δ / 4) * (x + δ / 4) ≤ x * x * PT + δ := by
      nlinarith [mul_nonneg hPTnn hδ.le, mul_nonneg hPTnn (sub_nonneg.2 hx2.le), hx1, hx2, mul_pos hδ hδ, mul_nonneg hPTnn (mul_nonneg hδ.le (sub_nonneg.2 hx2.le))]
    nlinarith
  linarith

end MoranYanPAC.Dev.Priv
end

section
set_option autoImplicit false

namespace MoranYanPAC.Dev.Disapp

open Finset

variable {Y : Type*} [DecidableEq Y]

theorem geom_part (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x < 1) (R : ℕ) :
    ∑ t ∈ Finset.Icc 1 R, x ^ t ≤ x / (1 - x) := by
  have h1 : ∑ t ∈ Finset.Icc 1 R, x ^ t = ∑ t ∈ Finset.range R, x ^ (t + 1) := by
    rw [Finset.range_eq_Ico, Finset.sum_Ico_add' (fun t => x ^ t) 0 R 1]
    simp [Finset.Icc, Finset.Ico]; rfl
  rw [h1]
  have h2 : ∑ t ∈ Finset.range R, x ^ (t + 1) = x * ∑ t ∈ Finset.range R, x ^ t := by
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun t _ => ?_; ring
  rw [h2]
  have h3 : ∑ t ∈ Finset.range R, x ^ t ≤ 1 / (1 - x) := by
    rw [geom_sum_eq hx1.ne]
    have h0 : 0 ≤ x ^ R := pow_nonneg hx0 R
    calc (x ^ R - 1) / (x - 1) = (1 - x ^ R) / (1 - x) := by
          rw [← neg_sub x 1, ← neg_sub (x ^ R) 1, neg_div_neg_eq]
      _ ≤ 1 / (1 - x) := div_le_div_of_nonneg_right (by linarith) (by linarith)
  calc x * ∑ t ∈ Finset.range R, x ^ t ≤ x * (1 / (1 - x)) := mul_le_mul_of_nonneg_left h3 hx0
    _ = x / (1 - x) := by ring


theorem disappear_bound (oS oT : Finset Y) (rank : Y → ℕ) (wS wT : Y → ℝ) (δ B : ℝ)
    (hδ : 0 < δ) (hδ1 : δ < 1) (hB : 1 ≤ B)
    (hTpos : ∀ h ∈ oT, 0 < wT h)
    (F : {g // g ∈ oS} → {h // h ∈ oT})
    (hF1 : ∀ g : {g // g ∈ oS}, g.val ∉ oT → rank g.val < rank (F g).val)
    (hcard : ∀ (h : {h // h ∈ oT}) (t : ℕ), 1 ≤ t →
      ((Finset.univ.filter (fun g : {g // g ∈ oS} =>
        (F g).val = h.val ∧ rank g.val + t = rank h.val)).card : ℝ) ≤ B ^ t)
    (hw : ∀ g : {g // g ∈ oS}, g.val ∉ oT →
      wS g.val ≤ wT (F g).val * (δ / (8 * B)) ^ (rank (F g).val - rank g.val)) :
    ∑ g ∈ oS \ oT, wS g ≤ δ / 4 * ∑ h ∈ oT, wT h := by
  classical
  set A : Finset {g // g ∈ oS} := Finset.univ.filter (fun g => g.val ∉ oT) with hA
  have hsum1 : ∑ g ∈ oS \ oT, wS g = ∑ g ∈ A, wS g.val := by
    rw [Finset.sdiff_eq_filter, Finset.sum_filter, ← Finset.sum_coe_sort oS, hA, Finset.sum_filter]
  rw [hsum1]
  have hfib := Finset.sum_fiberwise_of_maps_to (s := A) (t := (Finset.univ : Finset {h // h ∈ oT}))
    (g := F) (fun g _ => Finset.mem_univ _) (fun g => wS g.val)
  rw [← hfib]
  have hZT : ∑ h ∈ oT, wT h = ∑ h : {h // h ∈ oT}, wT h.val := (Finset.sum_coe_sort oT wT).symm
  rw [hZT, Finset.mul_sum]
  refine Finset.sum_le_sum fun h _ => ?_
  set R := rank h.val with hR
  set x : ℝ := δ / (8 * B) with hx
  have hx0 : 0 ≤ x := by positivity
  set Ah := A.filter (fun g => F g = h) with hAh
  have hmaps : ∀ g ∈ Ah, rank h.val - rank g.val ∈ Finset.Icc 1 R := by
    intro g hg
    have hg' := Finset.mem_filter.1 hg
    have hgA : g.val ∉ oT := (Finset.mem_filter.1 hg'.1).2
    have h1 := hF1 g hgA
    rw [hg'.2] at h1
    simp only [Finset.mem_Icc]; omega
  have step1 : ∑ g ∈ Ah, wS g.val ≤ ∑ g ∈ Ah, wT h.val * x ^ (rank h.val - rank g.val) := by
    refine Finset.sum_le_sum fun g hg => ?_
    have hg' := Finset.mem_filter.1 hg
    have hgA : g.val ∉ oT := (Finset.mem_filter.1 hg'.1).2
    have := hw g hgA
    rw [hg'.2] at this
    exact this
  refine step1.trans ?_
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  have step2 : ∀ t ∈ Finset.Icc 1 R,
      ∑ g ∈ Ah.filter (fun g => rank h.val - rank g.val = t), wT h.val * x ^ (rank h.val - rank g.val)
        ≤ wT h.val * (δ / 8) ^ t := by
    intro t ht
    have ht1 : 1 ≤ t := (Finset.mem_Icc.1 ht).1
    have : ∑ g ∈ Ah.filter (fun g => rank h.val - rank g.val = t), wT h.val * x ^ (rank h.val - rank g.val)
        = ((Ah.filter (fun g => rank h.val - rank g.val = t)).card : ℝ) * (wT h.val * x ^ t) := by
      rw [Finset.sum_congr rfl (g := fun _ => wT h.val * x ^ t) (fun g hg => by rw [(Finset.mem_filter.1 hg).2]),
        Finset.sum_const, nsmul_eq_mul]
    rw [this]
    have hc : ((Ah.filter (fun g => rank h.val - rank g.val = t)).card : ℝ) ≤ B ^ t := by
      refine le_trans ?_ (hcard h t ht1)
      refine Nat.cast_le.2 (Finset.card_le_card ?_)
      intro g hg
      have hg1 := Finset.mem_filter.1 hg
      have hg2 := Finset.mem_filter.1 hg1.1
      have hgA : g.val ∉ oT := (Finset.mem_filter.1 hg2.1).2
      have h1 := hF1 g hgA
      rw [hg2.2] at h1
      refine Finset.mem_filter.2 ⟨Finset.mem_univ _, by rw [hg2.2], ?_⟩
      omega
    have hwT : 0 < wT h.val := hTpos _ h.2
    have hBx : B * x = δ / 8 := by rw [hx]; field_simp
    calc ((Ah.filter (fun g => rank h.val - rank g.val = t)).card : ℝ) * (wT h.val * x ^ t)
        ≤ B ^ t * (wT h.val * x ^ t) := mul_le_mul_of_nonneg_right hc (by positivity)
      _ = wT h.val * (B * x) ^ t := by rw [mul_pow]; ring
      _ = wT h.val * (δ / 8) ^ t := by rw [hBx]
  refine (Finset.sum_le_sum step2).trans ?_
  rw [← Finset.mul_sum]
  have hg := geom_part (δ / 8) (by positivity) (by linarith) R
  have hwT : 0 < wT h.val := hTpos _ h.2
  have : (δ / 8) / (1 - δ / 8) ≤ δ / 4 := by
    rw [div_le_iff₀ (by linarith)]; nlinarith
  nlinarith

end MoranYanPAC.Dev.Disapp
end

section
set_option autoImplicit false
open scoped ENNReal

namespace MoranYanPAC.Dev.Gibbs

open MoranYanPAC.Main

theorem gibbs_prob {Y : Type*} [DecidableEq Y] (out : Finset Y) (hne : out.Nonempty) (f : Y → ℝ)
    (E : Set Y) [DecidablePred (· ∈ E)] :
    eventProbability (finiteGibbs out hne f) E =
      ENNReal.ofReal ((∑ h ∈ out.filter (· ∈ E), Real.exp (f h)) / ∑ h ∈ out, Real.exp (f h)) := by
  classical
  unfold eventProbability finiteGibbs
  rw [PMF.toOuterMeasure_map_apply, PMF.toOuterMeasure_apply]
  rw [tsum_fintype]
  simp only [Set.indicator, Set.mem_preimage, PMF.normalize_apply]
  have hZ : (∑' (h : ↥out), ENNReal.ofReal (Real.exp (f ↑h))) =
      ENNReal.ofReal (∑ h ∈ out, Real.exp (f h)) := by
    rw [tsum_fintype, Finset.sum_coe_sort out (fun h => ENNReal.ofReal (Real.exp (f h))),
      ENNReal.ofReal_sum_of_nonneg (fun _ _ => (Real.exp_pos _).le)]
  rw [hZ]
  have hZpos : 0 < ∑ h ∈ out, Real.exp (f h) := Finset.sum_pos (fun _ _ => Real.exp_pos _) hne
  have hN : (∑ b : ↥out, if (b : Y) ∈ E then ENNReal.ofReal (Real.exp (f ↑b)) else 0) =
      ENNReal.ofReal (∑ h ∈ out.filter (· ∈ E), Real.exp (f h)) := by
    rw [Finset.sum_coe_sort out (fun h => if h ∈ E then ENNReal.ofReal (Real.exp (f h)) else 0),
      ← Finset.sum_filter, ENNReal.ofReal_sum_of_nonneg (fun _ _ => (Real.exp_pos _).le)]
  have hc : ∀ b : ↥out, (if (b : Y) ∈ E then ENNReal.ofReal (Real.exp (f ↑b)) *
      (ENNReal.ofReal (∑ h ∈ out, Real.exp (f h)))⁻¹ else 0) =
      (if (b : Y) ∈ E then ENNReal.ofReal (Real.exp (f ↑b)) else 0) *
      (ENNReal.ofReal (∑ h ∈ out, Real.exp (f h)))⁻¹ := by
    intro b; split_ifs <;> simp
  rw [Finset.sum_congr rfl (fun b _ => hc b), ← Finset.sum_mul, hN,
    ENNReal.ofReal_div_of_pos hZpos, div_eq_mul_inv]

end MoranYanPAC.Dev.Gibbs
end

section
set_option autoImplicit false
open scoped ENNReal

namespace MoranYanPAC.Dev.T2

open MoranYanPAC.Main

variable {Z Y : Type*}

theorem weight_cmp (ε δ Δ B : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hΔ : 0 < Δ) (hB : 1 ≤ B) (sg sh rg rh : ℝ) (t : ℕ) (ht : 1 ≤ t) (hrt : rh = rg + t)
    (hs : |sg - sh| ≤ Δ) :
    Real.exp ((ε / (2 * Δ)) * (sg + rankBonus ε δ Δ B * rg)) ≤
      Real.exp ((ε / (2 * Δ)) * (sh + rankBonus ε δ Δ B * rh)) * (δ / (8 * B)) ^ t := by
  have hB0 : 0 < B := by linarith
  have hL : 0 < 8 * B / δ := by positivity
  have hab : (ε / (2 * Δ)) * rankBonus ε δ Δ B = ε / 2 + Real.log (8 * B / δ) := by
    unfold rankBonus; field_simp
  have h1 : (δ / (8 * B)) ^ t = Real.exp (-(Real.log (8 * B / δ)) * t) := by
    rw [neg_mul, Real.exp_neg, mul_comm (Real.log (8 * B / δ)) (t : ℝ), Real.exp_nat_mul, Real.exp_log hL,
      show δ / (8 * B) = (8 * B / δ)⁻¹ by field_simp, inv_pow]
  rw [h1, ← Real.exp_add]
  apply Real.exp_le_exp.2
  have h2 : (ε / (2 * Δ)) * (sg - sh) ≤ ε / 2 := by
    have := abs_le.1 hs
    calc (ε / (2 * Δ)) * (sg - sh) ≤ (ε / (2 * Δ)) * Δ :=
          mul_le_mul_of_nonneg_left this.2 (by positivity)
      _ = ε / 2 := by field_simp
  have h3 : (ε / (2 * Δ)) * (sg + rankBonus ε δ Δ B * rg) =
      (ε / (2 * Δ)) * (sg - sh) + (ε / (2 * Δ)) * sh + ((ε / (2 * Δ)) * rankBonus ε δ Δ B) * rg := by ring
  have h4 : (ε / (2 * Δ)) * (sh + rankBonus ε δ Δ B * rh) =
      (ε / (2 * Δ)) * sh + ((ε / (2 * Δ)) * rankBonus ε δ Δ B) * rh := by ring
  rw [h3, h4, hab, hrt]
  have ht' : (1 : ℝ) ≤ t := by exact_mod_cast ht
  have hlog : 0 ≤ Real.log (8 * B / δ) := Real.log_nonneg (by
    rw [le_div_iff₀ hδ]; nlinarith)
  nlinarith [mul_nonneg hlog (sub_nonneg.2 ht'), mul_nonneg hε.le (sub_nonneg.2 ht')]


theorem disapp_dir [DecidableEq Y] (M : StructuralData Z Y) (ε δ Δ B : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hδ : 0 < δ) (hδ1 : δ < 1) (hΔ : 0 < Δ) (hB : 1 ≤ B) (S T : List Z)
    (F : {g // g ∈ M.out S} → {h // h ∈ M.out T})
    (hF12 : ∀ g, (g.val ∈ M.out T → (F g).val = g.val) ∧
      (g.val ∉ M.out T → M.rank g.val < M.rank (F g).val))
    (hF3 : ∀ h : {h // h ∈ M.out T}, ∀ t : ℕ, 1 ≤ t →
      (({g : {g // g ∈ M.out S} | (F g).val = h.val ∧
        M.rank g.val + t = M.rank h.val}).encard : ℝ≥0∞) ≤ ENNReal.ofReal (B ^ t))
    (hF4 : ∀ g : {g // g ∈ M.out S}, |M.score S g.val - M.score T (F g).val| ≤ Δ) :
    ∑ g ∈ M.out S \ M.out T, Real.exp ((ε / (2 * Δ)) * (M.score S g + rankBonus ε δ Δ B * M.rank g)) ≤
      δ / 4 * ∑ h ∈ M.out T, Real.exp ((ε / (2 * Δ)) * (M.score T h + rankBonus ε δ Δ B * M.rank h)) := by
  refine Disapp.disappear_bound (M.out S) (M.out T) M.rank _ _ δ B hδ hδ1 hB
    (fun h _ => Real.exp_pos _) F (fun g hg => (hF12 g).2 hg) ?_ ?_
  · intro h t ht
    have h1 := hF3 h t ht
    have hset : {g : {g // g ∈ M.out S} | (F g).val = h.val ∧ M.rank g.val + t = M.rank h.val} =
        ↑(Finset.univ.filter (fun g : {g // g ∈ M.out S} =>
          (F g).val = h.val ∧ M.rank g.val + t = M.rank h.val)) := by
      ext g; simp
    rw [hset, Set.encard_coe_eq_coe_finsetCard] at h1
    have h2 : ((Finset.univ.filter (fun g : {g // g ∈ M.out S} =>
          (F g).val = h.val ∧ M.rank g.val + t = M.rank h.val)).card : ℝ≥0∞) ≤ ENNReal.ofReal (B ^ t) := by
      simpa using h1
    have h3 : ENNReal.ofReal (((Finset.univ.filter (fun g : {g // g ∈ M.out S} =>
          (F g).val = h.val ∧ M.rank g.val + t = M.rank h.val)).card : ℝ)) ≤ ENNReal.ofReal (B ^ t) := by
      rwa [ENNReal.ofReal_natCast]
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 h3
  · intro g hg
    have hr := (hF12 g).2 hg
    obtain ⟨t, ht⟩ : ∃ t, M.rank (F g).val = M.rank g.val + t := ⟨_, (Nat.add_sub_of_le hr.le).symm⟩
    have ht1 : 1 ≤ t := by omega
    have := weight_cmp ε δ Δ B hε hε1 hδ hδ1 hΔ hB (M.score S g.val) (M.score T (F g).val)
      (M.rank g.val : ℝ) (M.rank (F g).val : ℝ) t ht1 (by rw [ht]; push_cast; ring) (hF4 g)
    have h5 : M.rank (F g).val - M.rank g.val = t := by omega
    rw [h5]
    exact this


theorem neigh_symm {S T : List Z} (h : PrivLittlestone.IsInsDelNeighbor S T) :
    PrivLittlestone.IsInsDelNeighbor T S := by
  unfold PrivLittlestone.IsInsDelNeighbor at *
  exact h.symm

theorem privacy (M : StructuralData Z Y) (ε δ Δ B : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hδ : 0 < δ) (hδ1 : δ < 1) (hΔ : 0 < Δ) (hB : 1 ≤ B) (haxioms : StructuralAxioms M Δ B) :
    Private (structuralMechanism M ε δ Δ B) ε δ := by
  classical
  intro S T hn E
  obtain ⟨hs1, F, hF12, hF3, hF4⟩ := haxioms S T hn
  obtain ⟨hs1', F', hF12', hF3', hF4'⟩ := haxioms T S (neigh_symm hn)
  unfold structuralMechanism
  rw [Gibbs.gibbs_prob, Gibbs.gibbs_prob]
  have hmain := Priv.priv_real (M.out S) (M.out T)
    (fun h => Real.exp ((ε / (2 * Δ)) * (M.score S h + rankBonus ε δ Δ B * M.rank h)))
    (fun h => Real.exp ((ε / (2 * Δ)) * (M.score T h + rankBonus ε δ Δ B * M.rank h)))
    ε δ hε hε1 hδ hδ1 (fun h _ => Real.exp_pos _) (fun h _ => Real.exp_pos _)
    ⟨_, (M.nonempty S).choose_spec⟩ ⟨_, (M.nonempty T).choose_spec⟩
    (fun h _ => by
      rw [← Real.exp_add]
      refine Real.exp_le_exp.2 ?_
      have := abs_le.1 (hs1 h)
      have h2 : (ε / (2 * Δ)) * (M.score S h - M.score T h) ≤ ε / 2 := by
        calc (ε / (2 * Δ)) * (M.score S h - M.score T h) ≤ (ε / (2 * Δ)) * Δ :=
              mul_le_mul_of_nonneg_left this.2 (by positivity)
          _ = ε / 2 := by field_simp
      nlinarith)
    (fun h _ => by
      rw [← Real.exp_add]
      refine Real.exp_le_exp.2 ?_
      have := abs_le.1 (hs1 h)
      have h2 : (ε / (2 * Δ)) * (M.score T h - M.score S h) ≤ ε / 2 := by
        calc (ε / (2 * Δ)) * (M.score T h - M.score S h) ≤ (ε / (2 * Δ)) * Δ :=
              mul_le_mul_of_nonneg_left (by linarith [this.1]) (by positivity)
          _ = ε / 2 := by field_simp
      nlinarith)
    (disapp_dir M ε δ Δ B hε hε1 hδ hδ1 hΔ hB S T F hF12 hF3 hF4)
    (by
      have := disapp_dir M ε δ Δ B hε hε1 hδ hδ1 hΔ hB T S F' hF12' hF3' hF4'
      exact this) E
  have hnn : 0 ≤ (∑ h ∈ (M.out T).filter (· ∈ E),
      Real.exp ((ε / (2 * Δ)) * (M.score T h + rankBonus ε δ Δ B * M.rank h))) /
      ∑ h ∈ M.out T, Real.exp ((ε / (2 * Δ)) * (M.score T h + rankBonus ε δ Δ B * M.rank h)) :=
    div_nonneg (Finset.sum_nonneg fun _ _ => (Real.exp_pos _).le)
      (Finset.sum_nonneg fun _ _ => (Real.exp_pos _).le)
  rw [← ENNReal.ofReal_mul (Real.exp_pos ε).le,
    ← ENNReal.ofReal_add (mul_nonneg (Real.exp_pos ε).le hnn) hδ.le]
  exact ENNReal.ofReal_le_ofReal hmain


theorem utility (M : StructuralData Z Y) (ε δ Δ B : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hδ : 0 < δ) (hδ1 : δ < 1) (hΔ : 0 < Δ) (hB : 1 ≤ B) (S : List Z) (β : ℝ) (hβ : 0 < β)
    (hβ1 : β < 1) :
    ENNReal.ofReal (1 - β) ≤ eventProbability (structuralMechanism M ε δ Δ B S)
        {h | bestScore M S - (2 * Δ / ε) *
          ((rankRange M S : ℝ) * Real.log (16 * B / δ) +
            Real.log ((M.out S).card / β)) ≤ M.score S h} := by
  classical
  unfold structuralMechanism
  rw [Gibbs.gibbs_prob]
  refine ENNReal.ofReal_le_ofReal ?_
  set w : Y → ℝ := fun h => Real.exp ((ε / (2 * Δ)) * (M.score S h + rankBonus ε δ Δ B * M.rank h)) with hw
  set E : Set Y := {h | bestScore M S - (2 * Δ / ε) *
          ((rankRange M S : ℝ) * Real.log (16 * B / δ) +
            Real.log ((M.out S).card / β)) ≤ M.score S h} with hE
  have hne := M.nonempty S
  have hZpos : 0 < ∑ h ∈ M.out S, w h := Finset.sum_pos (fun _ _ => Real.exp_pos _) hne
  rw [le_div_iff₀ hZpos]
  obtain ⟨hstar, hstarmem, hstareq⟩ := Finset.exists_mem_eq_sup' hne (M.score S)
  have hbest : bestScore M S = M.score S hstar := by unfold bestScore; exact hstareq
  set N : ℝ := ((M.out S).card : ℝ) with hN
  have hNpos : 0 < N := by
    have := Finset.card_pos.2 hne
    rw [hN]; exact_mod_cast this
  -- split Z = N_E + bad
  have hsplit : ∑ h ∈ M.out S, w h =
      ∑ h ∈ (M.out S).filter (· ∈ E), w h + ∑ h ∈ (M.out S).filter (fun h => ¬ h ∈ E), w h :=
    (Finset.sum_filter_add_sum_filter_not _ _ _).symm
  have hstarle : w hstar ≤ ∑ h ∈ M.out S, w h :=
    Finset.single_le_sum (f := w) (fun _ _ => (Real.exp_pos _).le) hstarmem
  have hbad : ∀ h ∈ (M.out S).filter (fun h => ¬ h ∈ E), w h ≤ (β / N) * w hstar := by
    intro h hh
    have hh' := Finset.mem_filter.1 hh
    have hsc : M.score S h < bestScore M S - (2 * Δ / ε) *
          ((rankRange M S : ℝ) * Real.log (16 * B / δ) + Real.log (N / β)) := by
      have := hh'.2; simp only [hE, Set.mem_setOf_eq, not_le] at this; exact this
    have hrk : (M.rank h : ℝ) - M.rank hstar ≤ rankRange M S := by
      have h1 : M.rank h ≤ (M.out S).sup' hne M.rank := Finset.le_sup' _ hh'.1
      have h2 : (M.out S).inf' hne M.rank ≤ M.rank hstar := Finset.inf'_le _ hstarmem
      have h3 : (M.out S).inf' hne M.rank ≤ (M.out S).sup' hne M.rank :=
        (Finset.inf'_le _ hh'.1).trans h1
      unfold rankRange
      have : M.rank h ≤ ((M.out S).sup' hne M.rank - (M.out S).inf' hne M.rank) + M.rank hstar := by omega
      have h4 : ((M.rank h : ℕ) : ℝ) ≤ (((M.out S).sup' hne M.rank - (M.out S).inf' hne M.rank : ℕ) : ℝ)
          + M.rank hstar := by exact_mod_cast this
      linarith
    have hB0 : 0 < B := by linarith
    have hab : (ε / (2 * Δ)) * rankBonus ε δ Δ B = ε / 2 + Real.log (8 * B / δ) := by
      unfold rankBonus; field_simp
    have hlog16 : Real.log (16 * B / δ) = Real.log 2 + Real.log (8 * B / δ) := by
      rw [← Real.log_mul (by norm_num) (by positivity)]; congr 1; ring
    have hR : (0 : ℝ) ≤ rankRange M S := Nat.cast_nonneg _
    have hlog2 := Real.log_two_gt_d9
    have hexp : w h ≤ w hstar * (β / N) := by
      simp only [hw]
      have : Real.exp ((ε / (2 * Δ)) * (M.score S h + rankBonus ε δ Δ B * M.rank h)) =
          Real.exp ((ε / (2 * Δ)) * (M.score S hstar + rankBonus ε δ Δ B * M.rank hstar)) *
          Real.exp ((ε / (2 * Δ)) * (M.score S h - M.score S hstar) +
            ((ε / (2 * Δ)) * rankBonus ε δ Δ B) * ((M.rank h : ℝ) - M.rank hstar)) := by
        rw [← Real.exp_add]; congr 1; ring
      rw [this]
      refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
      have hbeta : β / N = Real.exp (-Real.log (N / β)) := by
        rw [Real.exp_neg, Real.exp_log (by positivity)]; field_simp
      rw [hbeta]
      refine Real.exp_le_exp.2 ?_
      rw [hbest] at hsc
      rw [hab]
      have e1 : (ε / (2 * Δ)) * (M.score S h - M.score S hstar) ≤
          -((ε / (2 * Δ)) * ((2 * Δ / ε) * ((rankRange M S : ℝ) * Real.log (16 * B / δ) +
            Real.log (N / β)))) := by
        have := mul_le_mul_of_nonneg_left (le_of_lt (by linarith : M.score S h - M.score S hstar <
          -((2 * Δ / ε) * ((rankRange M S : ℝ) * Real.log (16 * B / δ) + Real.log (N / β)))))
          (by positivity : (0 : ℝ) ≤ ε / (2 * Δ))
        linarith
      have e2 : (ε / (2 * Δ)) * ((2 * Δ / ε) * ((rankRange M S : ℝ) * Real.log (16 * B / δ) +
            Real.log (N / β))) = (rankRange M S : ℝ) * Real.log (16 * B / δ) + Real.log (N / β) := by
        field_simp
      rw [e2] at e1
      have e3 : (ε / 2 + Real.log (8 * B / δ)) * ((M.rank h : ℝ) - M.rank hstar) ≤
          (ε / 2 + Real.log (8 * B / δ)) * (rankRange M S : ℝ) := by
        refine mul_le_mul_of_nonneg_left hrk ?_
        have : 0 ≤ Real.log (8 * B / δ) := Real.log_nonneg (by rw [le_div_iff₀ hδ]; nlinarith)
        linarith
      rw [hlog16] at e1
      nlinarith [mul_nonneg hR (sub_nonneg.2 (le_of_lt (by linarith : ε / 2 < Real.log 2)))]
    linarith [mul_comm (β / N) (w hstar)]
  have hbadsum : ∑ h ∈ (M.out S).filter (fun h => ¬ h ∈ E), w h ≤ β * ∑ h ∈ M.out S, w h := by
    refine (Finset.sum_le_sum hbad).trans ?_
    rw [Finset.sum_const, nsmul_eq_mul]
    have hc : (((M.out S).filter (fun h => ¬ h ∈ E)).card : ℝ) ≤ N := by
      rw [hN]; exact_mod_cast Finset.card_filter_le _ _
    calc (((M.out S).filter (fun h => ¬ h ∈ E)).card : ℝ) * (β / N * w hstar) ≤ N * (β / N * w hstar) :=
          mul_le_mul_of_nonneg_right hc (by have := Real.exp_pos
                                                      ((ε / (2 * Δ)) * (M.score S hstar + rankBonus ε δ Δ B * M.rank hstar))
                                            positivity)
      _ = β * w hstar := by field_simp
      _ ≤ β * ∑ h ∈ M.out S, w h := mul_le_mul_of_nonneg_left hstarle hβ.le
  nlinarith

end MoranYanPAC.Dev.T2

namespace MoranYanPAC.Main

theorem chk_structural_exponential_mechanism {Z Y : Type*} (M : StructuralData Z Y)
    (ε δ Δ B : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hΔ : 0 < Δ) (hB : 1 ≤ B) (haxioms : StructuralAxioms M Δ B) :
    Private (structuralMechanism M ε δ Δ B) ε δ ∧
    ∀ (S : List Z) (β : ℝ), 0 < β → β < 1 →
      ENNReal.ofReal (1 - β) ≤ eventProbability (structuralMechanism M ε δ Δ B S)
        {h | bestScore M S - (2 * Δ / ε) *
          ((rankRange M S : ℝ) * Real.log (16 * B / δ) +
            Real.log ((M.out S).card / β)) ≤ M.score S h} :=
  ⟨Dev.T2.privacy M ε δ Δ B hε hε1 hδ hδ1 hΔ hB haxioms,
    fun S β hβ hβ1 => Dev.T2.utility M ε δ Δ B hε hε1 hδ hδ1 hΔ hB S β hβ hβ1⟩

end MoranYanPAC.Main
end

theorem solution : type_of% @MoranYanPAC.Main.chk_structural_exponential_mechanism := @MoranYanPAC.Main.chk_structural_exponential_mechanism
