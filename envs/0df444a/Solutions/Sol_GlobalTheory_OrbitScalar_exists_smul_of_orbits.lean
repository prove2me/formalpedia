-- Prove2me | solution 1 for GlobalTheory.OrbitScalar.exists_smul_of_orbits
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T19:17:28.647436+00:00
-- url     : https://prove2.me/submissions/d850cd65-34b6-40d2-9d8d-2843a1bf0c85

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_UnFree
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainPointBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FourierCoefficientDomain
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_ExistsSmulOfPreservesFrameOrbits
import Theorems.Thm_GlobalTheory_OrbitScalar_exists_mem_dom
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj
open scoped Matrix
namespace GlobalTheory.OrbitScalar
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
open NumberField in
open scoped Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} in
private lemma isOpen_dom_cubical_line_bundles (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) :
    IsOpen (X.dom : Set (X.Ψ → Fin r → Fin r → ℂ)) := by
  have hset : (X.dom : Set (X.Ψ → Fin r → Fin r → ℂ)) =
      ⋂ τ : X.Ψ, ({x | (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ).det ≠ 0} ∩
        ⋂ i : Fin (r + 1), {x | 0 < _root_.ReciprocityTheory.ChartRestriction.G.FD.psgn X.p0 i * (_root_.ReciprocityTheory.ChartRestriction.G.FD.dmin X.Gm x τ i).re}) := by
    ext x
    simp only [Set.mem_iInter, Set.mem_inter_iff, Set.mem_setOf_eq]
    rfl
  rw [hset]
  refine isOpen_iInter_of_finite fun τ => IsOpen.inter ?_ (isOpen_iInter_of_finite fun i => ?_)
  · refine isOpen_ne_fun ?_ continuous_const
    unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.mat
    fun_prop
  · refine isOpen_lt continuous_const (Continuous.mul continuous_const ?_)
    refine Complex.continuous_re.comp ?_
    unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.dmin _root_.ReciprocityTheory.ChartRestriction.G.FD.lminor _root_.ReciprocityTheory.ChartRestriction.G.FD.gram _root_.ReciprocityTheory.ChartRestriction.G.FD.hermC _root_.ReciprocityTheory.ChartRestriction.G.FD.col _root_.ReciprocityTheory.ChartRestriction.G.FD.mat
    fun_prop
open NumberField in
open scoped Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} in
private lemma exists_scalar_of_eigen_on_open {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (U : Set (Fin n → ℂ)) (hU : IsOpen U) (hne : U.Nonempty)
    (h : ∀ v ∈ U, ∃ c : ℂ, A *ᵥ v = c • v) : ∃ c : ℂ, ∀ w, A *ᵥ w = c • w := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact ⟨0, fun w => Subsingleton.elim _ _⟩
  obtain ⟨v0, hv0⟩ := hne
  obtain ⟨ε0, hε0, hb0⟩ := Metric.isOpen_iff.mp hU v0 hv0
  have hex : ∃ v1 ∈ U, v1 ≠ 0 := by
    by_cases hv : v0 = 0
    · subst hv
      refine ⟨((ε0 / 2 : ℝ) : ℂ) • Pi.single ⟨0, hn⟩ 1, hb0 ?_, ?_⟩
      · rw [Metric.mem_ball, dist_zero_right, norm_smul, Pi.norm_single, norm_one, mul_one,
          Complex.norm_real, Real.norm_of_nonneg (by positivity)]
        linarith
      · refine smul_ne_zero (by exact_mod_cast (by positivity : (ε0 / 2 : ℝ) ≠ 0)) ?_
        simp
    · exact ⟨v0, hv0, hv⟩
  obtain ⟨v1, hv1, hv1ne⟩ := hex
  obtain ⟨ε, hε, hb⟩ := Metric.isOpen_iff.mp hU v1 hv1
  obtain ⟨c0, hc0⟩ := h v1 hv1
  have hsmall : ∀ w, ‖w‖ < ε → A *ᵥ w = c0 • w := by
    intro w hw
    obtain ⟨a, ha⟩ := h (v1 + w) (hb (by simpa [Metric.mem_ball, dist_eq_norm] using hw))
    obtain ⟨b, hbq⟩ := h (v1 - w) (hb (by simpa [Metric.mem_ball, dist_eq_norm, norm_neg] using hw))
    have hsum : (a - c0) • (v1 + w) = (c0 - b) • (v1 - w) := by
      have h1 : A *ᵥ (v1 + w) + A *ᵥ (v1 - w) = (2 : ℂ) • (A *ᵥ v1) := by
        rw [← Matrix.mulVec_add, ← Matrix.mulVec_smul]
        congr 1
        module
      rw [ha, hbq, hc0] at h1
      linear_combination (norm := module) h1
    have hw' : A *ᵥ w = A *ᵥ (v1 + w) - A *ᵥ v1 := by
      rw [← Matrix.mulVec_sub]; congr 1; abel
    by_cases hac : a = c0
    · rw [hw', ha, hc0, hac]
      module
    · set k := (c0 - b) / (a - c0) with hk
      have hp : v1 + w = k • (v1 - w) := by
        have hne' : a - c0 ≠ 0 := sub_ne_zero.mpr hac
        rw [hk, div_eq_mul_inv, mul_comm, mul_smul, ← hsum, smul_smul, inv_mul_cancel₀ hne', one_smul]
      by_cases h1k : 1 + k = 0
      · exfalso
        have hk1 : k = -1 := by linear_combination h1k
        rw [hk1] at hp
        apply hv1ne
        have : (2 : ℂ) • v1 = 0 := by linear_combination (norm := module) hp
        simpa using this
      · have hwv : w = ((k - 1) / (1 + k)) • v1 := by
          have : (1 + k) • w = (k - 1) • v1 := by linear_combination (norm := module) hp
          rw [div_eq_mul_inv, mul_comm, mul_smul, ← this, smul_smul, inv_mul_cancel₀ h1k, one_smul]
        rw [hwv, Matrix.mulVec_smul, hc0, smul_comm]
  refine ⟨c0, fun w => ?_⟩
  set t : ℝ := ε / (2 * (‖w‖ + 1)) with ht
  have htpos : 0 < t := by positivity
  have htw : ‖(t : ℂ) • w‖ < ε := by
    rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg htpos.le, ht]
    rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    nlinarith [norm_nonneg w]
  have h2 := hsmall _ htw
  rw [Matrix.mulVec_smul, smul_comm] at h2
  have htne : (t : ℂ) ≠ 0 := by exact_mod_cast htpos.ne'
  exact smul_right_injective _ htne h2
open NumberField in
open scoped Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} in
private lemma exists_eq_smul_of_parallel_on_open {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ)
    (hB : B.det ≠ 0) (U : Set (Fin n → ℂ)) (hU : IsOpen U) (hne : U.Nonempty)
    (h : ∀ v ∈ U, ∀ i j, (A *ᵥ v) i * (B *ᵥ v) j = (A *ᵥ v) j * (B *ᵥ v) i) :
    ∃ c : ℂ, A = c • B := by
  have hBu : IsUnit B.det := isUnit_iff_ne_zero.mpr hB
  obtain ⟨c, hc⟩ := exists_scalar_of_eigen_on_open (B⁻¹ * A) U hU hne fun v hv => by
    by_cases hw : B *ᵥ v = 0
    · have hv0 : v = 0 := by
        have := congrArg (fun z => B⁻¹ *ᵥ z) hw
        simpa [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul B hBu] using this
      exact ⟨0, by simp [hv0]⟩
    · obtain ⟨k, hk⟩ := Function.ne_iff.mp hw
      have hk' : (B *ᵥ v) k ≠ 0 := by simpa using hk
      obtain ⟨c0, hAv⟩ : ∃ c0 : ℂ, A *ᵥ v = c0 • (B *ᵥ v) := by
        refine ⟨(A *ᵥ v) k / (B *ᵥ v) k, ?_⟩
        funext i
        have := h v hv i k
        simp only [Pi.smul_apply, smul_eq_mul]
        field_simp
        linear_combination this
      refine ⟨c0, ?_⟩
      rw [← Matrix.mulVec_mulVec, hAv, Matrix.mulVec_smul, Matrix.mulVec_mulVec,
        Matrix.nonsing_inv_mul B hBu, Matrix.one_mulVec]
  refine ⟨c, Matrix.toLin'.injective (LinearMap.ext fun w => ?_)⟩
  have h1 := hc w
  rw [Matrix.toLin'_apply, Matrix.toLin'_apply]
  have h2 := congrArg (fun z => B *ᵥ z) h1
  simp only [Matrix.mulVec_mulVec, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv B hBu,
    Matrix.one_mul, Matrix.mulVec_smul] at h2
  rw [h2]
  funext i
  simp [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]
end GlobalTheory.OrbitScalar
end

set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj
open scoped Matrix
open GlobalTheory GlobalTheory.OrbitScalar
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
open NumberField
open scoped Matrix
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
namespace GlobalTheory.OrbitScalar
namespace _root_.GlobalTheory.OrbitScalar
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E]
    [IsCMField E] (r : ℕ) (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) (γ : GL (Fin r) E),
    (∀ x ∈ X.dom, ∃ γ' ∈ X.Γ, ∃ b ∈ _root_.ReciprocityTheory.ChartRestriction.G.FD.Bor X.Ψ r, _root_.ReciprocityTheory.ChartRestriction.G.FD.lact γ x = _root_.ReciprocityTheory.ChartRestriction.G.FD.rmul (_root_.ReciprocityTheory.ChartRestriction.G.FD.lact γ' x) b) →
      ∃ γ' ∈ X.Γ, ∃ u : E, (γ' : Matrix (Fin r) (Fin r) E) = u • (γ : Matrix (Fin r) (Fin r) E) := by
  intro E _ _ _ r X γ hγ
  classical
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · exact ⟨1, X.Γ.one_mem, 0, Matrix.ext fun i _ => i.elim0⟩
  set i0 : Fin r := ⟨0, hr⟩ with hi0
  haveI : Countable E := (Module.finBasis ℚ E).equivFun.injective.countable
  haveI : Countable (GL (Fin r) E) :=
    Function.Injective.countable (f := fun g : GL (Fin r) E => fun i j => (g : Matrix (Fin r) (Fin r) E) i j)
      fun g h e => Units.ext (Matrix.ext fun i j => congrFun (congrFun e i) j)
  let col : (X.Ψ → Fin r → Fin r → ℂ) → X.Ψ → Fin r → ℂ := fun x τ a => x τ a i0
  let C : X.Γ → Set (X.Ψ → Fin r → Fin r → ℂ) := fun g => {x | ∀ τ : X.Ψ, ∀ i j,
    (((γ : Matrix (Fin r) (Fin r) E).map τ) *ᵥ col x τ) i *
      ((((g : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ) *ᵥ col x τ) j =
    (((γ : Matrix (Fin r) (Fin r) E).map τ) *ᵥ col x τ) j *
      ((((g : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ) *ᵥ col x τ) i}
  have hCclosed : ∀ g, IsClosed (C g) := fun g => by
    simp only [C, Set.setOf_forall]
    exact isClosed_iInter fun τ => isClosed_iInter fun i => isClosed_iInter fun j =>
      isClosed_eq (by fun_prop) (by fun_prop)
  let f : Option X.Γ → Set (X.Ψ → Fin r → Fin r → ℂ) := fun o =>
    o.elim (X.dom : Set (X.Ψ → Fin r → Fin r → ℂ))ᶜ C
  have hfc : ∀ o, IsClosed (f o) := by
    rintro (_ | g)
    · exact (isOpen_dom_cubical_line_bundles X).isClosed_compl
    · exact hCclosed g
  have hcover : ⋃ o, f o = Set.univ := by
    refine Set.eq_univ_of_forall fun x => ?_
    by_cases hx : x ∈ (X.dom : Set (X.Ψ → Fin r → Fin r → ℂ))
    · obtain ⟨g, hg, b, hb, heq⟩ := hγ x hx
      refine Set.mem_iUnion.mpr ⟨some ⟨g, hg⟩, ?_⟩
      show ∀ τ : X.Ψ, ∀ i j, _
      intro τ i j
      have hcol : ((γ : Matrix (Fin r) (Fin r) E).map τ) *ᵥ col x τ =
          b τ i0 i0 • (((g : Matrix (Fin r) (Fin r) E).map τ) *ᵥ col x τ) := by
        funext a
        have h := congrFun (congrFun (congrFun heq τ) a) i0
        unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.lact _root_.ReciprocityTheory.ChartRestriction.G.FD.rmul _root_.ReciprocityTheory.ChartRestriction.G.FD.mat at h
        simp only [Matrix.mul_apply, Matrix.of_apply] at h
        have hR : ∀ F : Fin r → ℂ, ∑ k, F k * b τ k i0 = F i0 * b τ i0 i0 := fun F =>
          Finset.sum_eq_single i0 (fun k _ hk => by
            rw [(hb τ).2 k i0 (Fin.lt_def.mpr (Nat.pos_of_ne_zero fun h0 => hk (Fin.ext h0))),
              mul_zero]) (by simp)
        rw [hR] at h
        simp only [Matrix.mulVec, dotProduct, col, Pi.smul_apply, smul_eq_mul, Matrix.of_apply,
          Matrix.mul_apply] at h ⊢
        rw [h, mul_comm]
        rfl
      rw [hcol]
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
    · exact Set.mem_iUnion.mpr ⟨none, hx⟩
  obtain ⟨x, hxdom, hxint⟩ := (dense_iUnion_interior_of_closed hfc hcover).inter_open_nonempty _
    (isOpen_dom_cubical_line_bundles X) (_root_.GlobalTheory.OrbitScalar.exists_mem_dom X)
  obtain ⟨o, ho⟩ := Set.mem_iUnion.mp hxint
  rcases o with _ | g
  · exact absurd hxdom (interior_subset ho)
  obtain ⟨τ0⟩ : Nonempty X.Ψ := by
    obtain σ : E →+* ℂ := Classical.arbitrary _
    by_cases hσ : σ ∈ X.Ψ
    · exact ⟨⟨σ, hσ⟩⟩
    · refine ⟨⟨ComplexEmbedding.conjugate σ, (X.cmType _).mpr ?_⟩⟩
      simpa [ComplexEmbedding.conjugate, star_star] using hσ
  let upd : (Fin r → ℂ) → X.Ψ → Fin r → Fin r → ℂ := fun v τ a c =>
    if τ = τ0 ∧ c = i0 then v a else x τ a c
  have hupd : Continuous upd := by
    refine continuous_pi fun τ => continuous_pi fun a => continuous_pi fun c => ?_
    by_cases h : τ = τ0 ∧ c = i0
    · simp only [upd, h, and_self, if_true]
      exact continuous_apply a
    · simp only [upd, h, if_false]
      exact continuous_const
  have hupdx : upd (col x τ0) = x := by
    funext τ a c
    by_cases h : τ = τ0 ∧ c = i0
    · obtain ⟨rfl, rfl⟩ := h
      simp [upd, col]
    · simp [upd, h]
  have hcolupd : ∀ v, col (upd v) τ0 = v := fun v => by
    funext a
    simp [upd, col]
  let U := upd ⁻¹' interior (f (some g))
  have hU : IsOpen U := isOpen_interior.preimage hupd
  have hUne : U.Nonempty := ⟨col x τ0, by simpa [U, hupdx] using ho⟩
  have hdet : (((g : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map (τ0 : E →+* ℂ)).det ≠ 0 := by
    have h := RingHom.map_det (τ0 : E →+* ℂ) ((g : GL (Fin r) E) : Matrix (Fin r) (Fin r) E)
    rw [RingHom.mapMatrix_apply] at h
    rw [← h]
    exact (map_ne_zero _).mpr
      ((Matrix.isUnit_iff_isUnit_det _).mp (g : GL (Fin r) E).isUnit).ne_zero
  obtain ⟨c, hc⟩ := exists_eq_smul_of_parallel_on_open _ _ hdet U hU hUne fun v hv i j => by
    have hmem : upd v ∈ C g := interior_subset hv
    have := hmem τ0 i j
    rwa [hcolupd] at this
  have hent : ∀ a b, (τ0 : E →+* ℂ) ((γ : Matrix (Fin r) (Fin r) E) a b) =
      c * (τ0 : E →+* ℂ) (((g : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) a b) := fun a b => by
    have h := congrFun (congrFun hc a) b
    simpa [Matrix.map_apply] using h
  haveI : Nonempty (Fin r) := ⟨i0⟩
  have hne0 : ∀ δ : GL (Fin r) E, (δ : Matrix (Fin r) (Fin r) E) ≠ 0 := fun δ h0 => by
    have h := (Matrix.isUnit_iff_isUnit_det _).mp δ.isUnit
    rw [h0, Matrix.det_zero] at h
    exact not_isUnit_zero h
  obtain ⟨k, l, hkl⟩ : ∃ k l, ((g : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) k l ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hne0 g (Matrix.ext hcon)
  set u0 : E := (γ : Matrix (Fin r) (Fin r) E) k l /
    ((g : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) k l with hu0def
  have hτkl : (τ0 : E →+* ℂ) (((g : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) k l) ≠ 0 :=
    (map_ne_zero _).mpr hkl
  have hcu : c = (τ0 : E →+* ℂ) u0 := by
    rw [hu0def, map_div₀, hent k l]
    field_simp
  have hγg : (γ : Matrix (Fin r) (Fin r) E) =
      u0 • ((g : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) :=
    Matrix.ext fun a b => (τ0 : E →+* ℂ).injective (by
      rw [hent, hcu, Matrix.smul_apply, smul_eq_mul, map_mul])
  have hu0 : u0 ≠ 0 := fun h0 => hne0 γ (by rw [hγg, h0, zero_smul])
  refine ⟨g, g.2, u0⁻¹, ?_⟩
  rw [hγg, smul_smul, inv_mul_cancel₀ hu0, one_smul]
end _root_.GlobalTheory.OrbitScalar
end GlobalTheory.OrbitScalar
