-- Prove2me | solution 1 for GlobalTheory.SW.polyDeriv_pairing_eq_zero_of_isHeat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:52:37.889621+00:00
-- url     : https://prove2.me/submissions/e92f63a8-81ab-4baa-9302-c8dc5218903f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_PolyDerivMonomialOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExhaustStatementPfA
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_MemAnalyticAtZeroOfEventuallyDifferentiableAt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_IsHeatThH
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_PolyDerivPairingEqZeroOfIsHeat
import Theorems.Thm_GlobalTheory_SCV_analyticOnNhd_of_differentiableOn
import Theorems.Thm_GlobalTheory_SW_ExpSum_imH_isHermitian
import Theorems.Thm_GlobalTheory_analyticAt_lineDerivList
import Theorems.Thm_GlobalTheory_dirPolyDeriv_eq_sum
import Theorems.Thm_GlobalTheory_lineDerivList_append
import Theorems.Thm_GlobalTheory_lineDerivList_comp_add_const
import Theorems.Thm_GlobalTheory_lineDerivList_comp_linearMap
import Theorems.Thm_GlobalTheory_lineDerivList_congr
import Theorems.Thm_GlobalTheory_lineDerivList_cons
import Theorems.Thm_GlobalTheory_lineDerivList_const_smul
import Theorems.Thm_GlobalTheory_lineDerivList_nil
import Theorems.Thm_GlobalTheory_lineDerivList_perm
import Theorems.Thm_GlobalTheory_lineDerivList_sum
import Theorems.Thm_GlobalTheory_lineDerivList_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_itD_nil
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_jof_polyDeriv_sum
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_pdTerm_eq_itD
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_polyDeriv_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_polyDeriv_monomial_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_polyDeriv_smul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.lineDerivList_nil
attribute [local simp] GlobalTheory.lineDerivList_zero


section
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real Classical
namespace GlobalTheory.SW.HeatJet
variable {E : Type} [Field E] [NumberField E] [IsCMField E] (Ψ : Finset (E →+* ℂ)) {n N : ℕ}
end GlobalTheory.SW.HeatJet
open Matrix Complex NumberField Filter Topology in
open scoped ComplexConjugate ComplexOrder Real Classical in
private lemma continuous_star_dotProduct_imH_mulVec {N : ℕ} :
    Continuous (fun p : Matrix (Fin N) (Fin N) ℂ × (Fin N → ℂ) =>
      star p.2 ⬝ᵥ (_root_.GlobalTheory.SW.imH p.1 *ᵥ p.2)) := by
  unfold _root_.GlobalTheory.SW.imH
  fun_prop
open Matrix Complex NumberField Filter Topology in
open scoped ComplexConjugate ComplexOrder Real Classical in
private lemma isOpen_setOf_posDef_imH {N : ℕ} :
    IsOpen {A : Matrix (Fin N) (Fin N) ℂ | (_root_.GlobalTheory.SW.imH A).PosDef} := by
  rw [isOpen_iff_mem_nhds]
  intro A hA
  have hK : IsCompact (Metric.sphere (0 : Fin N → ℂ) 1) := isCompact_sphere 0 1
  have hev : ∀ᶠ B in 𝓝 A, ∀ y ∈ Metric.sphere (0 : Fin N → ℂ) 1,
      0 < (star y ⬝ᵥ (_root_.GlobalTheory.SW.imH B *ᵥ y)).re := by
    refine hK.eventually_forall_of_forall_eventually fun y hy => ?_
    have hy0 : y ≠ 0 := by
      rintro rfl
      simp at hy
    have hpos := (posDef_iff_dotProduct_mulVec.mp hA).2 hy0
    have : 0 < (star y ⬝ᵥ (_root_.GlobalTheory.SW.imH A *ᵥ y)).re := (Complex.pos_iff.mp hpos).1
    exact (Complex.continuous_re.comp continuous_star_dotProduct_imH_mulVec).continuousAt.eventually
      (lt_mem_nhds this)
  filter_upwards [hev] with B hB
  have hH := _root_.GlobalTheory.SW.ExpSum.imH_isHermitian B
  refine PosDef.of_dotProduct_mulVec_pos hH fun x hx => ?_
  have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
  set c : ℂ := ((‖x‖⁻¹ : ℝ) : ℂ)
  have hy : c • x ∈ Metric.sphere (0 : Fin N → ℂ) 1 := by
    simp [c, norm_smul, hn.ne']
  have h1 := hB _ hy
  have hscale : star (c • x) ⬝ᵥ (_root_.GlobalTheory.SW.imH B *ᵥ (c • x)) =
      ((‖x‖⁻¹ ^ 2 : ℝ) : ℂ) * (star x ⬝ᵥ (_root_.GlobalTheory.SW.imH B *ᵥ x)) := by
    simp only [star_smul, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, c,
      Complex.star_def, Complex.conj_ofReal, smul_eq_mul]
    push_cast
    ring
  rw [hscale, Complex.re_ofReal_mul] at h1
  refine Complex.pos_iff.mpr ⟨?_, ?_⟩
  · exact pos_of_mul_pos_right h1 (by positivity)
  · exact (hH.im_star_dotProduct_mulVec_self x).symm
open Matrix Complex NumberField Filter Topology in
open scoped ComplexConjugate ComplexOrder Real Classical in
private lemma polyDeriv_mul_sum_pairs_eq_sum_lineDerivList {σ ι W : Type*} [Fintype ι] [NormedAddCommGroup W] [NormedSpace ℂ W]
    (A : MvPolynomial σ ℂ) (i j : ι → σ) (u : σ → W) {F : W → ℂ} {x : W}
    (hF : ∀ᶠ y in 𝓝 x, AnalyticAt ℂ F y) :
    _root_.ReciprocityTheory.ChartRestriction.G.I2.polyDeriv (A * ∑ k, MvPolynomial.X (i k) * MvPolynomial.X (j k)) u F x =
      ∑ m ∈ A.support, MvPolynomial.coeff m A * _root_.GlobalTheory.lineDerivList ℂ ((Finsupp.toMultiset m).toList.map u)
        (fun y => ∑ k, _root_.GlobalTheory.lineDerivList ℂ [u (i k), u (j k)] F y) x := by
  have hFx : AnalyticAt ℂ F x := hF.self_of_nhds
  conv_lhs => rw [MvPolynomial.as_sum A, Finset.sum_mul]
  rw [_root_.ReciprocityTheory.ChartRestriction.G.I2.jof_polyDeriv_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Finset.mul_sum, _root_.ReciprocityTheory.ChartRestriction.G.I2.jof_polyDeriv_sum]
  have hG : ∀ k, AnalyticAt ℂ (_root_.GlobalTheory.lineDerivList ℂ [u (i k), u (j k)] F) x := fun k =>
    _root_.GlobalTheory.analyticAt_lineDerivList hFx _
  rw [_root_.GlobalTheory.lineDerivList_sum Finset.univ (fun k _ => hG k), Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hmon : MvPolynomial.monomial m (MvPolynomial.coeff m A) * (MvPolynomial.X (i k) * MvPolynomial.X (j k)) =
      MvPolynomial.coeff m A • MvPolynomial.monomial (m + Finsupp.single (i k) 1 + Finsupp.single (j k) 1) 1 := by
    simp only [MvPolynomial.X, MvPolynomial.monomial_mul, MvPolynomial.smul_monomial, smul_eq_mul, mul_one, add_assoc]
  rw [hmon, _root_.ReciprocityTheory.ChartRestriction.G.I2.polyDeriv_smul]
  congr 1
  have hl : (((Finsupp.toMultiset m).toList ++ [i k, j k] : List σ) : Multiset σ) =
      Finsupp.toMultiset (m + Finsupp.single (i k) 1 + Finsupp.single (j k) 1) := by
    simp [Finsupp.toMultiset_add, Finsupp.toMultiset_single, add_assoc]
    rw [← Multiset.coe_add, Multiset.coe_toList]
    exact Multiset.add_cons (i k) _ {j k}
  rw [_root_.GlobalTheory.dirPolyDeriv_monomial_eq_lineDerivList hl u hFx, List.map_append, _root_.GlobalTheory.lineDerivList_append]
  rfl
open Matrix Complex NumberField Filter Topology in
open scoped ComplexConjugate ComplexOrder Real Classical in
private lemma polyDeriv_eq_sum_coeff_lineDerivList_of_analyticAt {σ W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W]
    (P : MvPolynomial σ ℂ) (u : σ → W) {F : W → ℂ} {x : W} (hF : AnalyticAt ℂ F x) :
    _root_.ReciprocityTheory.ChartRestriction.G.I2.polyDeriv P u F x = ∑ m ∈ P.support,
      MvPolynomial.coeff m P * _root_.GlobalTheory.lineDerivList ℂ ((Finsupp.toMultiset m).toList.map u) F x := by
  rw [_root_.GlobalTheory.dirPolyDeriv_eq_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [_root_.GlobalTheory.dirPolyDeriv_monomial_eq_lineDerivList (Multiset.coe_toList _) u hF]
open Matrix Complex NumberField Filter Topology in
open scoped ComplexConjugate ComplexOrder Real Classical in
private lemma sum_coeff_lineDerivList_eq_lineDeriv_polyDeriv {σ W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W]
    (A : MvPolynomial σ ℂ) (u : σ → W) {F : W → ℂ} {x : W} (z : W)
    (hF : ∀ᶠ y in 𝓝 x, AnalyticAt ℂ F y) :
    ∑ m ∈ A.support, MvPolynomial.coeff m A * _root_.GlobalTheory.lineDerivList ℂ ((Finsupp.toMultiset m).toList.map u)
        (_root_.GlobalTheory.lineDerivList ℂ [z] F) x = lineDeriv ℂ (fun y => _root_.ReciprocityTheory.ChartRestriction.G.I2.polyDeriv A u F y) x z := by
  have hFx : AnalyticAt ℂ F x := hF.self_of_nhds
  have heq : (fun y => _root_.ReciprocityTheory.ChartRestriction.G.I2.polyDeriv A u F y) =ᶠ[𝓝 x] fun y => ∑ m ∈ A.support,
      MvPolynomial.coeff m A * _root_.GlobalTheory.lineDerivList ℂ ((Finsupp.toMultiset m).toList.map u) F y :=
    hF.mono fun y hy => polyDeriv_eq_sum_coeff_lineDerivList_of_analyticAt A u hy
  have h1 := (_root_.GlobalTheory.lineDerivList_congr (𝕜 := ℂ) heq [z]).self_of_nhds
  have hl : lineDeriv ℂ (fun y => _root_.ReciprocityTheory.ChartRestriction.G.I2.polyDeriv A u F y) x z = _root_.GlobalTheory.lineDerivList ℂ [z] (fun y => _root_.ReciprocityTheory.ChartRestriction.G.I2.polyDeriv A u F y) x := by
    simp [_root_.GlobalTheory.lineDerivList_cons, _root_.GlobalTheory.lineDerivList_nil]
  rw [hl, h1, _root_.GlobalTheory.lineDerivList_sum A.support (F := fun m y => MvPolynomial.coeff m A * _root_.GlobalTheory.lineDerivList ℂ ((Finsupp.toMultiset m).toList.map u) F y) (fun m _ => analyticAt_const.mul (_root_.GlobalTheory.analyticAt_lineDerivList hFx _))]
  refine Finset.sum_congr rfl fun m _ => ?_
  have hc := congrFun (_root_.GlobalTheory.lineDerivList_const_smul (𝕜 := ℂ) [z] (MvPolynomial.coeff m A)
    (_root_.GlobalTheory.lineDerivList ℂ ((Finsupp.toMultiset m).toList.map u) F)) x
  simp only [smul_eq_mul] at hc
  rw [hc]
  congr 1
  rw [← _root_.GlobalTheory.lineDerivList_append, ← _root_.GlobalTheory.lineDerivList_append]
  exact _root_.GlobalTheory.lineDerivList_perm hFx List.perm_append_comm
open Matrix Complex NumberField Filter Topology in
open scoped ComplexConjugate ComplexOrder Real Classical in
private lemma polyDeriv_comp_linearMap_add_of_analyticAt {σ W W' : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W]
    [NormedAddCommGroup W'] [NormedSpace ℂ W'] [FiniteDimensional ℂ W'] (P : MvPolynomial σ ℂ)
    (u : σ → W') (L : W' →ₗ[ℂ] W) (c : W) {F : W → ℂ} (hF : AnalyticAt ℂ F c) :
    _root_.ReciprocityTheory.ChartRestriction.G.I2.polyDeriv P u (fun w => F (L w + c)) 0 = _root_.ReciprocityTheory.ChartRestriction.G.I2.polyDeriv P (fun i => L (u i)) F c := by
  have hL : AnalyticAt ℂ (fun w => F (L w + c)) 0 := by
    have h1 : AnalyticAt ℂ (fun w => L w + c) 0 :=
      (LinearMap.toContinuousLinearMap L).analyticAt 0 |>.add analyticAt_const
    have hF' : AnalyticAt ℂ F (L 0 + c) := by simpa using hF
    exact AnalyticAt.comp (g := F) (f := fun w => L w + c) (x := 0) hF' h1
  rw [polyDeriv_eq_sum_coeff_lineDerivList_of_analyticAt P u hL, polyDeriv_eq_sum_coeff_lineDerivList_of_analyticAt P _ hF]
  refine Finset.sum_congr rfl fun m _ => ?_
  congr 1
  rw [_root_.GlobalTheory.lineDerivList_comp_linearMap (F := fun q => F (q + c)), _root_.GlobalTheory.lineDerivList_comp_add_const]
  beta_reduce
  rw [map_zero, zero_add, List.map_map]
  rfl
end

set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real Classical
open Matrix Complex NumberField Filter Topology
open scoped ComplexConjugate ComplexOrder Real Classical
namespace _root_.GlobalTheory.SW
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Finset (E →+* ℂ)) (n N : ℕ) (D : _root_.GlobalTheory.SW.CM Ψ N N → _root_.GlobalTheory.SW.CM Ψ n N → _root_.GlobalTheory.SW.CM Ψ n N → ℂ), _root_.GlobalTheory.SW.IsHeat Ψ D → (∀ Z ∈ _root_.GlobalTheory.SW.Hn Ψ N, D Z 0 0 = 0) → ∀ Z ∈ _root_.GlobalTheory.SW.Hn Ψ N, ∀ s : MvPolynomial (Ψ × Fin N × Fin N) ℂ, _root_.ReciprocityTheory.ChartRestriction.G.I2.polyDeriv (MvPolynomial.aeval (fun v : Ψ × Fin N × Fin N => ∑ k, (MvPolynomial.X (v.1, false, k, v.2.1) * MvPolynomial.X (v.1, true, k, v.2.2) : MvPolynomial (Ψ × Bool × Fin n × Fin N) ℂ)) s) (fun v => (Pi.single v 1 : Ψ × Bool × Fin n × Fin N → ℂ)) (fun w : Ψ × Bool × Fin n × Fin N → ℂ => D Z (fun τ => Matrix.of fun k a => w (τ, false, k, a)) (fun τ => Matrix.of fun k a => w (τ, true, k, a))) 0 = 0 := by
  intro E _ _ _ Ψ n N D hD h0 Z hZ s
  obtain ⟨hdiff, hheat⟩ := hD
  have hU : IsOpen {p : ((Ψ → Fin N → Fin N → ℂ) × (Ψ → Fin n → Fin N → ℂ) × (Ψ → Fin n → Fin N → ℂ)) | p.1 ∈ _root_.GlobalTheory.SW.Hn Ψ N} := by
    have : {p : ((Ψ → Fin N → Fin N → ℂ) × (Ψ → Fin n → Fin N → ℂ) × (Ψ → Fin n → Fin N → ℂ)) | p.1 ∈ _root_.GlobalTheory.SW.Hn Ψ N} = ⋂ τ : Ψ, (fun p : ((Ψ → Fin N → Fin N → ℂ) × (Ψ → Fin n → Fin N → ℂ) × (Ψ → Fin n → Fin N → ℂ)) => (p.1 τ : Matrix (Fin N) (Fin N) ℂ)) ⁻¹' {A | (_root_.GlobalTheory.SW.imH A).PosDef} := by
      ext p
      simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage]
      exact Iff.rfl
    rw [this]
    exact isOpen_iInter_of_finite fun τ => isOpen_setOf_posDef_imH.preimage ((continuous_apply τ).comp continuous_fst)
  have han : AnalyticOnNhd ℂ (fun p : ((Ψ → Fin N → Fin N → ℂ) × (Ψ → Fin n → Fin N → ℂ) × (Ψ → Fin n → Fin N → ℂ)) => D p.1 p.2.1 p.2.2) {p : ((Ψ → Fin N → Fin N → ℂ) × (Ψ → Fin n → Fin N → ℂ) × (Ψ → Fin n → Fin N → ℂ)) | p.1 ∈ _root_.GlobalTheory.SW.Hn Ψ N} := _root_.GlobalTheory.SCV.analyticOnNhd_of_differentiableOn hU hdiff
  have hanU : ∀ p : ((Ψ → Fin N → Fin N → ℂ) × (Ψ → Fin n → Fin N → ℂ) × (Ψ → Fin n → Fin N → ℂ)), p.1 ∈ _root_.GlobalTheory.SW.Hn Ψ N → ∀ᶠ y in 𝓝 p, AnalyticAt ℂ (fun p : ((Ψ → Fin N → Fin N → ℂ) × (Ψ → Fin n → Fin N → ℂ) × (Ψ → Fin n → Fin N → ℂ)) => D p.1 p.2.1 p.2.2) y :=
    fun p hp => Filter.eventually_of_mem (hU.mem_nhds hp) fun y hy => han y hy
  let ew : Ψ × Bool × Fin n × Fin N → ((Ψ → Fin N → Fin N → ℂ) × (Ψ → Fin n → Fin N → ℂ) × (Ψ → Fin n → Fin N → ℂ)) := fun w => _root_.GlobalTheory.SW.HeatJet.emb Ψ (Pi.single w 1)
  let ez : Ψ × Fin N × Fin N → ((Ψ → Fin N → Fin N → ℂ) × (Ψ → Fin n → Fin N → ℂ) × (Ψ → Fin n → Fin N → ℂ)) := fun v => ((fun σ => if σ = v.1 then (Matrix.single v.2.1 v.2.2 (1 : ℂ) : Fin N → Fin N → ℂ) else 0 : Ψ → Fin N → Fin N → ℂ), 0, 0)
  have hheat' : ∀ p : ((Ψ → Fin N → Fin N → ℂ) × (Ψ → Fin n → Fin N → ℂ) × (Ψ → Fin n → Fin N → ℂ)), p.1 ∈ _root_.GlobalTheory.SW.Hn Ψ N → ∀ v : Ψ × Fin N × Fin N,
      ∑ k, _root_.GlobalTheory.lineDerivList ℂ [ew (v.1, false, k, v.2.1), ew (v.1, true, k, v.2.2)] (fun p : ((Ψ → Fin N → Fin N → ℂ) × (Ψ → Fin n → Fin N → ℂ) × (Ψ → Fin n → Fin N → ℂ)) => D p.1 p.2.1 p.2.2) p =
        (2 * Real.pi * Complex.I) * _root_.GlobalTheory.lineDerivList ℂ [ez v] (fun p : ((Ψ → Fin N → Fin N → ℂ) × (Ψ → Fin n → Fin N → ℂ) × (Ψ → Fin n → Fin N → ℂ)) => D p.1 p.2.1 p.2.2) p := by
    intro p hp v
    have h := hheat p.1 hp p.2.1 p.2.2 v.1 v.2.1 v.2.2
    have e1 : ∀ s : ℂ, p + s • ez v = ((show Ψ → Fin N → Fin N → ℂ from fun σ => (show Ψ → Matrix (Fin N) (Fin N) ℂ from p.1) σ + if σ = v.1 then single v.2.1 v.2.2 s else 0), p.2.1, p.2.2) := by
      intro s
      refine Prod.ext ?_ (Prod.ext ?_ ?_)
      · funext σ i j
        change p.1 σ i j + s * (if σ = v.1 then (single v.2.1 v.2.2 (1 : ℂ) : Matrix (Fin N) (Fin N) ℂ) else 0) i j = p.1 σ i j + (if σ = v.1 then (single v.2.1 v.2.2 s : Matrix (Fin N) (Fin N) ℂ) else 0) i j
        by_cases hσ : σ = v.1
        · rw [if_pos hσ, if_pos hσ]
          simp only [Matrix.single_apply]
          split_ifs <;> simp
        · rw [if_neg hσ, if_neg hσ]
          simp
      · funext σ i j
        change p.2.1 σ i j + s * 0 = p.2.1 σ i j
        simp
      · funext σ i j
        change p.2.2 σ i j + s * 0 = p.2.2 σ i j
        simp
    have e2 : ∀ k : Fin n, ∀ s t : ℂ, p + s • ew (v.1, false, k, v.2.1) + t • ew (v.1, true, k, v.2.2) =
        (p.1, (show Ψ → Fin n → Fin N → ℂ from fun σ => (show Ψ → Matrix (Fin n) (Fin N) ℂ from p.2.1) σ + if σ = v.1 then single k v.2.1 s else 0),
          (show Ψ → Fin n → Fin N → ℂ from fun σ => (show Ψ → Matrix (Fin n) (Fin N) ℂ from p.2.2) σ + if σ = v.1 then single k v.2.2 t else 0)) := by
      intro k s t
      refine Prod.ext ?_ (Prod.ext ?_ ?_)
      · funext σ i j
        change p.1 σ i j + s * 0 + t * 0 = p.1 σ i j
        simp
      · funext σ i j
        change p.2.1 σ i j + s * (Pi.single (v.1, false, k, v.2.1) (1 : ℂ) : Ψ × Bool × Fin n × Fin N → ℂ) (σ, false, i, j) + t * (Pi.single (v.1, true, k, v.2.2) (1 : ℂ) : Ψ × Bool × Fin n × Fin N → ℂ) (σ, false, i, j) = p.2.1 σ i j + (if σ = v.1 then (single k v.2.1 s : Matrix (Fin n) (Fin N) ℂ) else 0) i j
        by_cases hσ : σ = v.1
        · rw [if_pos hσ]
          subst hσ
          by_cases hi : i = k <;> by_cases hj : j = v.2.1 <;> simp [Matrix.single_apply, Pi.single_apply, hi, hj, eq_comm (a := k), eq_comm (a := v.2.1)]
        · rw [if_neg hσ]
          simp [Pi.single_apply, hσ]
      · funext σ i j
        change p.2.2 σ i j + s * (Pi.single (v.1, false, k, v.2.1) (1 : ℂ) : Ψ × Bool × Fin n × Fin N → ℂ) (σ, true, i, j) + t * (Pi.single (v.1, true, k, v.2.2) (1 : ℂ) : Ψ × Bool × Fin n × Fin N → ℂ) (σ, true, i, j) = p.2.2 σ i j + (if σ = v.1 then (single k v.2.2 t : Matrix (Fin n) (Fin N) ℂ) else 0) i j
        by_cases hσ : σ = v.1
        · rw [if_pos hσ]
          subst hσ
          by_cases hi : i = k <;> by_cases hj : j = v.2.2 <;> simp [Matrix.single_apply, Pi.single_apply, hi, hj, eq_comm (a := k), eq_comm (a := v.2.2)]
        · rw [if_neg hσ]
          simp [Pi.single_apply, hσ]
    have l1 : _root_.GlobalTheory.lineDerivList ℂ [ez v] (fun p : ((Ψ → Fin N → Fin N → ℂ) × (Ψ → Fin n → Fin N → ℂ) × (Ψ → Fin n → Fin N → ℂ)) => D p.1 p.2.1 p.2.2) p = deriv (fun s : ℂ => D (fun σ => (show Ψ → Matrix (Fin N) (Fin N) ℂ from p.1) σ + if σ = v.1 then single v.2.1 v.2.2 s else 0) p.2.1 p.2.2) 0 := by
      simp only [_root_.GlobalTheory.lineDerivList_cons, _root_.GlobalTheory.lineDerivList_nil, lineDeriv]
      congr 1
      funext s
      rw [e1 s]
    have l2 : ∀ k : Fin n, _root_.GlobalTheory.lineDerivList ℂ [ew (v.1, false, k, v.2.1), ew (v.1, true, k, v.2.2)] (fun p : ((Ψ → Fin N → Fin N → ℂ) × (Ψ → Fin n → Fin N → ℂ) × (Ψ → Fin n → Fin N → ℂ)) => D p.1 p.2.1 p.2.2) p = deriv (fun s : ℂ => deriv (fun t : ℂ => D p.1 (fun σ => (show Ψ → Matrix (Fin n) (Fin N) ℂ from p.2.1) σ + if σ = v.1 then single k v.2.1 s else 0) fun σ => (show Ψ → Matrix (Fin n) (Fin N) ℂ from p.2.2) σ + if σ = v.1 then single k v.2.2 t else 0) 0) 0 := by
      intro k
      simp only [_root_.GlobalTheory.lineDerivList_cons, _root_.GlobalTheory.lineDerivList_nil, lineDeriv]
      congr 1
      funext s
      congr 1
      funext t
      rw [e2 k s t]
    rw [l1, h]
    exact Finset.sum_congr rfl fun k _ => l2 k
  have key : ∀ s : MvPolynomial (Ψ × Fin N × Fin N) ℂ, ∀ p : ((Ψ → Fin N → Fin N → ℂ) × (Ψ → Fin n → Fin N → ℂ) × (Ψ → Fin n → Fin N → ℂ)), p.1 ∈ _root_.GlobalTheory.SW.Hn Ψ N → p.2 = 0 →
      _root_.ReciprocityTheory.ChartRestriction.G.I2.polyDeriv (MvPolynomial.aeval (fun v : Ψ × Fin N × Fin N => ∑ k, (MvPolynomial.X (v.1, false, k, v.2.1) * MvPolynomial.X (v.1, true, k, v.2.2) : MvPolynomial (Ψ × Bool × Fin n × Fin N) ℂ)) s) ew (fun p : ((Ψ → Fin N → Fin N → ℂ) × (Ψ → Fin n → Fin N → ℂ) × (Ψ → Fin n → Fin N → ℂ)) => D p.1 p.2.1 p.2.2) p = 0 := by
    intro s
    induction s using MvPolynomial.induction_on with
    | C a =>
      intro p hp hp0
      rw [MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq, MvPolynomial.C_apply, show MvPolynomial.monomial (0 : (Ψ × Bool × Fin n × Fin N) →₀ ℕ) a = a • MvPolynomial.monomial 0 1 by rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one], _root_.ReciprocityTheory.ChartRestriction.G.I2.polyDeriv_smul, _root_.ReciprocityTheory.ChartRestriction.G.I2.polyDeriv_monomial_one, _root_.ReciprocityTheory.ChartRestriction.G.I2.pdTerm_eq_itD]
      simp only [Finsupp.toMultiset_zero, Multiset.toList_zero, List.map_nil, _root_.ReciprocityTheory.ChartRestriction.G.I2.itD_nil]
      obtain ⟨p1, p2⟩ := p
      simp only at hp0
      subst hp0
      exact mul_eq_zero_of_right a (h0 p1 hp)
    | add A B hA hB =>
      intro p hp hp0
      rw [map_add, _root_.ReciprocityTheory.ChartRestriction.G.I2.polyDeriv_add, hA p hp hp0, hB p hp hp0, add_zero]
    | mul_X A v ih =>
      intro p hp hp0
      rw [map_mul, MvPolynomial.aeval_X]
      have hstep := polyDeriv_mul_sum_pairs_eq_sum_lineDerivList (MvPolynomial.aeval (fun v : Ψ × Fin N × Fin N => ∑ k, (MvPolynomial.X (v.1, false, k, v.2.1) * MvPolynomial.X (v.1, true, k, v.2.2) : MvPolynomial (Ψ × Bool × Fin n × Fin N) ℂ)) A) (fun k => (v.1, false, k, v.2.1)) (fun k => (v.1, true, k, v.2.2)) ew (hanU p hp)
      rw [hstep]
      have hev : (fun y => ∑ k, _root_.GlobalTheory.lineDerivList ℂ [ew (v.1, false, k, v.2.1), ew (v.1, true, k, v.2.2)] (fun p : ((Ψ → Fin N → Fin N → ℂ) × (Ψ → Fin n → Fin N → ℂ) × (Ψ → Fin n → Fin N → ℂ)) => D p.1 p.2.1 p.2.2) y) =ᶠ[𝓝 p]
          fun y => (2 * Real.pi * Complex.I) • _root_.GlobalTheory.lineDerivList ℂ [ez v] (fun p : ((Ψ → Fin N → Fin N → ℂ) × (Ψ → Fin n → Fin N → ℂ) × (Ψ → Fin n → Fin N → ℂ)) => D p.1 p.2.1 p.2.2) y :=
        Filter.eventually_of_mem (hU.mem_nhds hp) fun y hy => by simpa [smul_eq_mul] using hheat' y hy v
      have hsum : ∀ m, _root_.GlobalTheory.lineDerivList ℂ ((Finsupp.toMultiset m).toList.map ew)
            (fun y => ∑ k, _root_.GlobalTheory.lineDerivList ℂ [ew (v.1, false, k, v.2.1), ew (v.1, true, k, v.2.2)] (fun p : ((Ψ → Fin N → Fin N → ℂ) × (Ψ → Fin n → Fin N → ℂ) × (Ψ → Fin n → Fin N → ℂ)) => D p.1 p.2.1 p.2.2) y) p =
          (2 * Real.pi * Complex.I) * _root_.GlobalTheory.lineDerivList ℂ ((Finsupp.toMultiset m).toList.map ew) (_root_.GlobalTheory.lineDerivList ℂ [ez v] (fun p : ((Ψ → Fin N → Fin N → ℂ) × (Ψ → Fin n → Fin N → ℂ) × (Ψ → Fin n → Fin N → ℂ)) => D p.1 p.2.1 p.2.2)) p := by
        intro m
        rw [(_root_.GlobalTheory.lineDerivList_congr hev _).self_of_nhds, _root_.GlobalTheory.lineDerivList_const_smul]
        simp only [smul_eq_mul]
      simp only [hsum]
      simp only [mul_left_comm _ (2 * Real.pi * Complex.I : ℂ), ← Finset.mul_sum]
      rw [sum_coeff_lineDerivList_eq_lineDeriv_polyDeriv _ ew (ez v) (hanU p hp)]
      have hline : (fun t : ℂ => (fun y => _root_.ReciprocityTheory.ChartRestriction.G.I2.polyDeriv (MvPolynomial.aeval (fun v : Ψ × Fin N × Fin N => ∑ k, (MvPolynomial.X (v.1, false, k, v.2.1) * MvPolynomial.X (v.1, true, k, v.2.2) : MvPolynomial (Ψ × Bool × Fin n × Fin N) ℂ)) A) ew (fun p : ((Ψ → Fin N → Fin N → ℂ) × (Ψ → Fin n → Fin N → ℂ) × (Ψ → Fin n → Fin N → ℂ)) => D p.1 p.2.1 p.2.2) y) (p + t • ez v)) =ᶠ[𝓝 (0 : ℂ)] fun _ => (0 : ℂ) := by
        have hc : Continuous fun t : ℂ => p + t • ez v := by fun_prop
        have hmem : {p : ((Ψ → Fin N → Fin N → ℂ) × (Ψ → Fin n → Fin N → ℂ) × (Ψ → Fin n → Fin N → ℂ)) | p.1 ∈ _root_.GlobalTheory.SW.Hn Ψ N} ∈ 𝓝 (p + (0 : ℂ) • ez v) := by
          simpa using hU.mem_nhds hp
        filter_upwards [hc.continuousAt.preimage_mem_nhds hmem] with t ht
        refine ih _ ht ?_
        simp [ez, hp0]
      rw [lineDeriv, Filter.EventuallyEq.deriv_eq hline, deriv_const, mul_zero]
  have hG : (fun w : Ψ × Bool × Fin n × Fin N → ℂ => D Z (fun τ => Matrix.of fun k a => w (τ, false, k, a)) (fun τ => Matrix.of fun k a => w (τ, true, k, a))) = fun w => (fun q : ((Ψ → Fin N → Fin N → ℂ) × (Ψ → Fin n → Fin N → ℂ) × (Ψ → Fin n → Fin N → ℂ)) => D q.1 q.2.1 q.2.2) ((_root_.GlobalTheory.SW.HeatJet.emb Ψ : (Ψ × Bool × Fin n × Fin N → ℂ) →ₗ[ℂ] ((Ψ → Fin N → Fin N → ℂ) × (Ψ → Fin n → Fin N → ℂ) × (Ψ → Fin n → Fin N → ℂ))) w + ((show Ψ → Fin N → Fin N → ℂ from Z), 0, 0)) := by
    funext w
    simp only [_root_.GlobalTheory.SW.HeatJet.emb, LinearMap.coe_mk, AddHom.coe_mk, Prod.fst_add, Prod.snd_add, zero_add, add_zero]
    rw [show (0 + (show Ψ → Fin N → Fin N → ℂ from Z)) = Z from zero_add _]
    rfl
  rw [hG]
  refine (polyDeriv_comp_linearMap_add_of_analyticAt (u := fun v => (Pi.single v 1 : Ψ × Bool × Fin n × Fin N → ℂ)) (L := (_root_.GlobalTheory.SW.HeatJet.emb Ψ : (Ψ × Bool × Fin n × Fin N → ℂ) →ₗ[ℂ] ((Ψ → Fin N → Fin N → ℂ) × (Ψ → Fin n → Fin N → ℂ) × (Ψ → Fin n → Fin N → ℂ)))) (c := ((show Ψ → Fin N → Fin N → ℂ from Z), 0, 0)) (F := fun q : ((Ψ → Fin N → Fin N → ℂ) × (Ψ → Fin n → Fin N → ℂ) × (Ψ → Fin n → Fin N → ℂ)) => D q.1 q.2.1 q.2.2) _ (hanU _ hZ).self_of_nhds).trans ?_
  exact key s _ hZ rfl
end _root_.GlobalTheory.SW
