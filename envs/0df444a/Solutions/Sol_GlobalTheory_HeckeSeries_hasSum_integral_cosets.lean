-- Prove2me | solution 1 for GlobalTheory.HeckeSeries.hasSum_integral_cosets
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:25:46.36257+00:00
-- url     : https://prove2.me/submissions/215d0b30-26da-49dd-b08d-067f7a1e1c06

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_PairwiseDisjointCell
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasBoundedSumsOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_PowDvdOfHermMatEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_HasSumHeckeSeriesBorelSphericalIntegralCosets
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_CompleteHomogeneousBound_WeightedSummable_mul
import Theorems.Thm_GlobalTheory_Doubling_flatSec_self
import Theorems.Thm_GlobalTheory_Doubling_val_aOf
import Theorems.Thm_GlobalTheory_Doubling_val_leviOf
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_SatakeTrivialRangeBound_one_lt_resCard
import Theorems.Thm_GlobalTheory_LGrp_HasGJValue_unique
import Theorems.Thm_GlobalTheory_LGrp_HasGJ_unique
import Theorems.Thm_GlobalTheory_LGrp_checkFun_apply
import Theorems.Thm_GlobalTheory_LGrp_checkFun_checkFun
import Theorems.Thm_GlobalTheory_LGrp_lFactor_singleton
import Theorems.Thm_GlobalTheory_LGrp_lFactor_zero
import Theorems.Thm_GlobalTheory_LGrp_nabs_det_of_mem_KO
import Theorems.Thm_GlobalTheory_LGrp_nabs_eq_zpow
import Theorems.Thm_GlobalTheory_Published_UnramifiedDoublingGL_hasSum
import Theorems.Thm_GlobalTheory_SatakeBound_apply_hermGL
import Theorems.Thm_GlobalTheory_SatakeBound_card_hermIdx
import Theorems.Thm_GlobalTheory_SatakeBound_exists_hermMat
import Theorems.Thm_GlobalTheory_SatakeBound_hermGL_injective
import Theorems.Thm_GlobalTheory_SatakeBound_val_hermGL
import Theorems.Thm_GlobalTheory_SmGL_IsSmoothChar_mul
import Theorems.Thm_GlobalTheory_SmGL_ord_eq_zero_iff
import Theorems.Thm_GlobalTheory_SplitWeil_iwasawa_blockTriangular
import Theorems.Thm_GlobalTheory_SplitWeil_nabs_uniformiser
import Theorems.Thm_GlobalTheory_SplitWeil_one_lt_resCard
import Theorems.Thm_GlobalTheory_WeilM_IsTilde_unique
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks
attribute [local simp] GlobalTheory.Doubling.flatSec_self
attribute [local simp] GlobalTheory.Doubling.val_aOf
attribute [local simp] GlobalTheory.Doubling.val_leviOf
attribute [local simp] GlobalTheory.LGrp.checkFun_apply
attribute [local simp] GlobalTheory.LGrp.checkFun_checkFun
attribute [local simp] GlobalTheory.LGrp.lFactor_singleton
attribute [local simp] GlobalTheory.LGrp.lFactor_zero


section
open MeasureTheory ValuativeRel GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SatakeBound GlobalTheory.GLDoubling
noncomputable section
namespace GlobalTheory.HeckeSeries
section Cosets
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}
  {p : 𝒪[k]}
end Cosets
open MeasureTheory ValuativeRel in
private theorem hermGL_coset_out_entries_integral {k : Type} [Field k] [ValuativeRel k]
    [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ} {p : 𝒪[k]} (hp : Irreducible p)
    (a : Fin n → ℕ) (c : _root_.GlobalTheory.SatakeBound.HermIdx p a) :
    ∀ i j, (((_root_.GlobalTheory.SatakeBound.hermGL hp a c : GL (Fin n) k ⧸ _root_.GlobalTheory.SplitWeil.KO k (Fin n)).out :
      GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i j ∈ 𝒪[k] := by
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul (_root_.GlobalTheory.SplitWeil.KO k (Fin n))
    (_root_.GlobalTheory.SatakeBound.hermGL hp a c)
  have hint := ((_root_.GlobalTheory.SplitFlip.mem_KO_iff (h : GL (Fin n) k)).1 h.2).1
  intro i j
  rw [hh, Matrix.GeneralLinearGroup.coe_mul, Matrix.mul_apply]
  refine Subring.sum_mem _ fun l _ => Subring.mul_mem _ ?_ (hint l j)
  rw [_root_.GlobalTheory.SatakeBound.val_hermGL]
  exact ((_root_.GlobalTheory.SatakeBound.hermMat p a c) i l).2
open MeasureTheory ValuativeRel in
private theorem exists_hermGL_coset_eq_of_integral {k : Type} [Field k] [ValuativeRel k]
    [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ} {p : 𝒪[k]} (hp : Irreducible p)
    (g : GL (Fin n) k) (hg : ∀ i j, (g : Matrix (Fin n) (Fin n) k) i j ∈ 𝒪[k]) :
    ∃ a c, ((_root_.GlobalTheory.SatakeBound.hermGL hp a c : GL (Fin n) k) :
        GL (Fin n) k ⧸ _root_.GlobalTheory.SplitWeil.KO k (Fin n)) = (g : GL (Fin n) k ⧸ _) := by
  obtain ⟨b, hb, w, hw, hgbw⟩ :=
    _root_.GlobalTheory.SplitWeil.iwasawa_blockTriangular k (Fin n) (fun i => (i : ℕ)) g
  have hbint : ∀ i j, (b : Matrix (Fin n) (Fin n) k) i j ∈ 𝒪[k] := by
    have hbg : b = g * w⁻¹ := by rw [hgbw]; group
    have hwinv := ((_root_.GlobalTheory.SplitFlip.mem_KO_iff w).1 hw).2
    intro i j
    rw [hbg, Matrix.GeneralLinearGroup.coe_mul, Matrix.mul_apply]
    exact Subring.sum_mem _ fun l _ => Subring.mul_mem _ (hg i l) (hwinv l j)
  let b' : Matrix (Fin n) (Fin n) 𝒪[k] :=
    Matrix.of fun i j => ⟨(b : Matrix (Fin n) (Fin n) k) i j, hbint i j⟩
  have hlow : ∀ i j, j < i → b' i j = 0 := fun i j h => Subtype.ext (hb h)
  have hdiag : ∀ i, b' i i ≠ 0 := by
    intro i h
    have hb' : (b : Matrix (Fin n) (Fin n) k).BlockTriangular id := fun i j h => hb h
    have hdet := Matrix.det_of_upperTriangular hb'
    have hne : (b : Matrix (Fin n) (Fin n) k).det ≠ 0 := by
      rw [← Matrix.GeneralLinearGroup.val_det_apply]
      exact Units.ne_zero _
    apply hne
    rw [hdet]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (congrArg Subtype.val h)
  obtain ⟨a, c, W, hW⟩ := _root_.GlobalTheory.SatakeBound.exists_hermMat hp b' hlow hdiag
  refine ⟨a, c, ?_⟩
  let Wk : GL (Fin n) k := Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) W
  have hWk : Wk ∈ _root_.GlobalTheory.SplitWeil.KO k (Fin n) := by
    rw [_root_.GlobalTheory.SplitFlip.mem_KO_iff]
    constructor
    · intro i j
      exact ((W : Matrix (Fin n) (Fin n) 𝒪[k]) i j).2
    · intro i j
      rw [show Wk⁻¹ = Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) W⁻¹ from (map_inv _ _).symm]
      exact ((W⁻¹ : GL (Fin n) 𝒪[k]) i j).2
  have hhnf : _root_.GlobalTheory.SatakeBound.hermGL hp a c = b * Wk := by
    ext i j
    rw [_root_.GlobalTheory.SatakeBound.val_hermGL, hW, Matrix.GeneralLinearGroup.coe_mul, RingHom.mapMatrix_apply,
      Matrix.map_apply, Matrix.mul_apply, Matrix.mul_apply, map_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [map_mul]
    rfl
  rw [hhnf, hgbw, QuotientGroup.eq]
  convert mul_mem (inv_mem hWk) hw using 1
  group
open MeasureTheory ValuativeRel in
private theorem ord_eq_of_nabs_eq_resCard_zpow_neg {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {x : kˣ} {m : ℤ}
    (hx : _root_.GlobalTheory.SplitWeil.nabs k x = (_root_.GlobalTheory.SplitWeil.resCard k : ℝ) ^ (-m)) :
    _root_.GlobalTheory.SmGL.ord k x = m := by
  have hq : (1 : ℝ) < _root_.GlobalTheory.SplitWeil.resCard k := by
    exact_mod_cast _root_.GlobalTheory.SplitWeil.one_lt_resCard k
  rw [_root_.GlobalTheory.LGrp.nabs_eq_zpow] at hx
  have := zpow_right_injective₀ (by linarith) hq.ne' hx
  linarith
open MeasureTheory ValuativeRel in
private theorem ord_det_hermGL_mul_eq_sum {k : Type} [Field k] [ValuativeRel k]
    [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ} {p : 𝒪[k]} (hp : Irreducible p)
    (a : Fin n → ℕ) (c : _root_.GlobalTheory.SatakeBound.HermIdx p a) {w : GL (Fin n) k}
    (hw : w ∈ _root_.GlobalTheory.SplitWeil.KO k (Fin n)) :
    _root_.GlobalTheory.SmGL.ord k (Matrix.GeneralLinearGroup.det (_root_.GlobalTheory.SatakeBound.hermGL hp a c * w)) =
      ∑ i, (a i : ℤ) := by
  have hp0 : (p : k) ≠ 0 := by
    intro h
    exact hp.ne_zero (Subtype.ext h)
  set u : kˣ := Units.mk0 (p : k) hp0 with hu
  have hu1 : _root_.GlobalTheory.SmGL.ord k u = 1 := by
    apply ord_eq_of_nabs_eq_resCard_zpow_neg
    rw [_root_.GlobalTheory.SplitWeil.nabs_uniformiser hp (x := u) rfl, zpow_neg, zpow_one]
  have hupow : ∀ m : ℕ, _root_.GlobalTheory.SmGL.ord k (u ^ m) = m := by
    intro m
    induction m with
    | zero =>
      rw [pow_zero]
      exact _root_.GlobalTheory.SmGL.ord_eq_zero_iff.2 (by simp)
    | succ m ih => rw [pow_succ, _root_.GlobalTheory.SmGL.ord_mul, ih, hu1]; push_cast; ring
  have hw0 : _root_.GlobalTheory.SmGL.ord k (Matrix.GeneralLinearGroup.det w) = 0 := by
    apply ord_eq_of_nabs_eq_resCard_zpow_neg
    rw [_root_.GlobalTheory.GLDoubling.nabs_det_of_mem_KO hw]
    simp
  have hdet : Matrix.GeneralLinearGroup.det (_root_.GlobalTheory.SatakeBound.hermGL hp a c) = u ^ (∑ i, a i) := by
    ext
    rw [Matrix.GeneralLinearGroup.val_det_apply, _root_.GlobalTheory.SatakeBound.val_hermGL, RingHom.mapMatrix_apply,
      show ((_root_.GlobalTheory.SatakeBound.hermMat p a c).map (algebraMap 𝒪[k] k)).det =
        algebraMap 𝒪[k] k (_root_.GlobalTheory.SatakeBound.hermMat p a c).det from (RingHom.map_det _ _).symm,
      _root_.GlobalTheory.SatakeBound.det_hermMat]
    simp [u]
    rfl
  rw [map_mul, _root_.GlobalTheory.SmGL.ord_mul, hw0, hdet, hupow]
  push_cast
  ring
open MeasureTheory ValuativeRel in
private theorem hasSum_prod_pow_eq_prod_one_sub_inv : ∀ (n : ℕ) (β : Fin n → ℂ), (∀ i, ‖β i‖ < 1) →
    Summable (fun a : Fin n → ℕ => ‖∏ i, β i ^ a i‖) ∧
      HasSum (fun a : Fin n → ℕ => ∏ i, β i ^ a i) (∏ i, (1 - β i)⁻¹)
  | 0, β, _ => by
    refine ⟨Summable.of_finite, ?_⟩
    simpa using (hasSum_fintype (fun a : Fin 0 → ℕ => (1 : ℂ)))
  | n + 1, β, hβ => by
    obtain ⟨hs, hh⟩ := hasSum_prod_pow_eq_prod_one_sub_inv n (fun i => β i.succ) (fun i => hβ i.succ)
    have hg : HasSum (fun m : ℕ => β 0 ^ m) (1 - β 0)⁻¹ := hasSum_geometric_of_norm_lt_one (hβ 0)
    have hgn : Summable (fun m : ℕ => ‖β 0 ^ m‖) := by
      simpa [norm_pow] using summable_geometric_of_lt_one (norm_nonneg _) (hβ 0)
    have hprodn := Summable.mul_norm hgn hs
    have hprod := hg.mul hh (Summable.of_norm hprodn)
    let e : ℕ × (Fin n → ℕ) ≃ (Fin (n + 1) → ℕ) := Fin.consEquiv fun _ => ℕ
    have hfe : ∀ x : ℕ × (Fin n → ℕ), ∏ i, β i ^ (e x) i = β 0 ^ x.1 * ∏ i, β i.succ ^ x.2 i := by
      intro x
      rw [Fin.prod_univ_succ]
      simp [e, Fin.consEquiv]
    refine ⟨?_, ?_⟩
    · refine (e.summable_iff.1 ?_)
      refine hprodn.congr fun x => ?_
      simp only [Function.comp_apply, hfe]
    · rw [Fin.prod_univ_succ]
      refine (e.hasSum_iff.1 ?_)
      refine hprod.congr_fun fun x => ?_
      simp only [Function.comp_apply, hfe]
end GlobalTheory.HeckeSeries
end
end

set_option autoImplicit false
open MeasureTheory ValuativeRel GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SatakeBound GlobalTheory.GLDoubling
noncomputable section
open GlobalTheory GlobalTheory.HeckeSeries
open MeasureTheory ValuativeRel
namespace GlobalTheory.HeckeSeries
namespace _root_.GlobalTheory.HeckeSeries
theorem _root_.solution : ∀ (k : Type) [Field k] [ValuativeRel k]
    [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (γ : Fin n → ℂ)
    (φ : GL (Fin n) k → ℂ), _root_.GlobalTheory.SatakeBound.IsBorelSph k γ φ → ∀ X : ℂ,
    (∀ i : Fin n, ‖(_root_.GlobalTheory.SplitWeil.resCard k : ℂ) ^ (n - 1 - (i : ℕ)) * γ i * X‖ < 1) →
    HasSum (fun c : {c : GL (Fin n) k ⧸ _root_.GlobalTheory.SplitWeil.KO k (Fin n) //
        (∀ i j, (c.out : GL (Fin n) k).1 i j ∈ 𝒪[k])} =>
      X ^ (_root_.GlobalTheory.SmGL.ord k (Matrix.GeneralLinearGroup.det c.1.out)).toNat * φ c.1.out)
      (∏ i : Fin n, (1 - (_root_.GlobalTheory.SplitWeil.resCard k : ℂ) ^ (n - 1 - (i : ℕ)) * γ i * X)⁻¹) := by
  intro k _ _ _ _ n γ φ hφ X hX
  classical
  obtain ⟨p, hp⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[k]
  let F : (Σ a : Fin n → ℕ, _root_.GlobalTheory.SatakeBound.HermIdx p a) →
      {c : GL (Fin n) k ⧸ _root_.GlobalTheory.SplitWeil.KO k (Fin n) //
        (∀ i j, (c.out : GL (Fin n) k).1 i j ∈ 𝒪[k])} := fun x =>
    ⟨(_root_.GlobalTheory.SatakeBound.hermGL hp x.1 x.2 : GL (Fin n) k ⧸ _), hermGL_coset_out_entries_integral hp x.1 x.2⟩
  have hF : Function.Bijective F := by
    refine ⟨fun x y h => _root_.GlobalTheory.SatakeBound.hermGL_injective hp (congrArg Subtype.val h), fun s => ?_⟩
    obtain ⟨a, c, h⟩ := exists_hermGL_coset_eq_of_integral hp s.1.out s.2
    refine ⟨⟨a, c⟩, Subtype.ext ?_⟩
    change ((_root_.GlobalTheory.SatakeBound.hermGL hp a c : GL (Fin n) k) : GL (Fin n) k ⧸ _) = s.1
    rw [h]
    exact QuotientGroup.out_eq' s.1
  rw [← (Equiv.ofBijective F hF).hasSum_iff]
  set β : Fin n → ℂ := fun i => (_root_.GlobalTheory.SplitWeil.resCard k : ℂ) ^ (n - 1 - (i : ℕ)) * γ i * X
    with hβ
  have hterm : ∀ x : (Σ a : Fin n → ℕ, _root_.GlobalTheory.SatakeBound.HermIdx p a),
      X ^ (_root_.GlobalTheory.SmGL.ord k
        (Matrix.GeneralLinearGroup.det (F x).1.out)).toNat * φ (F x).1.out =
        ∏ i, (γ i * X) ^ x.1 i := by
    intro x
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul (_root_.GlobalTheory.SplitWeil.KO k (Fin n))
      (_root_.GlobalTheory.SatakeBound.hermGL hp x.1 x.2)
    have hord := ord_det_hermGL_mul_eq_sum hp x.1 x.2 h.2
    have hval := _root_.GlobalTheory.SatakeBound.apply_hermGL hp hφ x.1 x.2
    change X ^ (_root_.GlobalTheory.SmGL.ord k (Matrix.GeneralLinearGroup.det
      (Quotient.out ((_root_.GlobalTheory.SatakeBound.hermGL hp x.1 x.2 : GL (Fin n) k) :
        GL (Fin n) k ⧸ _root_.GlobalTheory.SplitWeil.KO k (Fin n))))).toNat *
      φ (Quotient.out ((_root_.GlobalTheory.SatakeBound.hermGL hp x.1 x.2 : GL (Fin n) k) :
        GL (Fin n) k ⧸ _root_.GlobalTheory.SplitWeil.KO k (Fin n))) = _
    rw [hval, hh, hord, show (∑ i, (x.1 i : ℤ)) = ((∑ i, x.1 i : ℕ) : ℤ) by push_cast; rfl,
      Int.toNat_natCast, ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun i _ => by rw [mul_pow, mul_comm]
  have hcard : ∀ a : Fin n → ℕ, (Nat.card (_root_.GlobalTheory.SatakeBound.HermIdx p a) : ℂ) *
      ∏ i, (γ i * X) ^ a i = ∏ i, β i ^ a i := by
    intro a
    rw [_root_.GlobalTheory.SatakeBound.card_hermIdx hp a]
    push_cast
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun i _ => by simp only [hβ, mul_assoc, mul_pow]
  have hfin : ∀ a : Fin n → ℕ, Finite (_root_.GlobalTheory.SatakeBound.HermIdx p a) := by
    intro a
    apply Nat.finite_of_card_ne_zero
    rw [_root_.GlobalTheory.SatakeBound.card_hermIdx hp a]
    exact Finset.prod_ne_zero_iff.2 fun i _ => pow_ne_zero _ (pow_ne_zero _
      (by have := _root_.GlobalTheory.SplitWeil.one_lt_resCard k; omega))
  obtain ⟨hsn, hsum⟩ := hasSum_prod_pow_eq_prod_one_sub_inv n β hX
  have hfib : ∀ a : Fin n → ℕ, ∑' c : _root_.GlobalTheory.SatakeBound.HermIdx p a, ∏ i, (γ i * X) ^ a i =
      ∏ i, β i ^ a i := by
    intro a
    rw [tsum_const, nsmul_eq_mul, hcard]
  have hsig : Summable (fun x : (Σ a : Fin n → ℕ, _root_.GlobalTheory.SatakeBound.HermIdx p a) =>
      ‖∏ i, (γ i * X) ^ x.1 i‖) := by
    rw [summable_sigma_of_nonneg (fun _ => norm_nonneg _)]
    refine ⟨fun a => Summable.of_finite, hsn.congr fun a => ?_⟩
    symm
    show ∑' _ : _root_.GlobalTheory.SatakeBound.HermIdx p a, ‖∏ i, (γ i * X) ^ a i‖ = _
    rw [tsum_const, nsmul_eq_mul, ← hcard, norm_mul, Complex.norm_natCast]
  have hs := hsig.of_norm
  have h2 := hs.hasSum.sigma (fun a => (Summable.of_finite).hasSum)
  simp only [hfib] at h2
  have hval := hsum.unique h2
  have hfinal : HasSum (fun x : (Σ a : Fin n → ℕ, _root_.GlobalTheory.SatakeBound.HermIdx p a) =>
      ∏ i, (γ i * X) ^ x.1 i) (∏ i, (1 - β i)⁻¹) := by
    rw [hval]
    exact hs.hasSum
  refine hfinal.congr_fun fun x => ?_
  exact hterm x
end _root_.GlobalTheory.HeckeSeries
end GlobalTheory.HeckeSeries
