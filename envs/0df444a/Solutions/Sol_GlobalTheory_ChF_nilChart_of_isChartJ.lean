-- Prove2me | solution 1 for GlobalTheory.ChF.nilChart_of_isChartJ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:34:46.557859+00:00
-- url     : https://prove2.me/submissions/9e283a5f-bb79-4f05-a84d-e28df9c55cd5

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartFH
import Definitions.Def_ReciprocityTheory_DualLattices_TowerZeroSurjective
import Definitions.Def_ReciprocityTheory_DualLattices_LinPairStatement
import Definitions.Def_ReciprocityTheory_DualLattices_LengthDegreeAbelianVariety
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_LePreimageOfNil
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Clauses
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TeichmullerDepth_IsEigBasisIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_NEvalSqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_IsUniversalChartOfFormalGroupChart
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_GermEvalOneStandardPointSelf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ExistsToJetEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_NilChartOfIsChartJ
import Theorems.Thm_GlobalTheory_ChF_nv_calculus
import Theorems.Thm_GlobalTheory_ChartBaseChange_exists_pt_of_aug
import Theorems.Thm_GlobalTheory_ChartBaseChange_fib_cond
import Theorems.Thm_GlobalTheory_ChartBaseChange_fib_ker
import Theorems.Thm_GlobalTheory_ChartBaseChange_pt_eps_self
import Theorems.Thm_GlobalTheory_ChartUniv_jetAug_eq
import Theorems.Thm_GlobalTheory_ChartUniv_univ_all
import Theorems.Thm_GlobalTheory_JetSer_jet_mk_eq_iff
import Theorems.Thm_GlobalTheory_evBasic_nEval_eq_tEval
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_exists_chart
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_jetAug_zR
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_jetLift_zR
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_jet_ext
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_ker_jetAug_pow
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_pt_injective
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_pt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_zR_mem_ker
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_chart
import Theorems.Thm_ReciprocityTheory_PGsh_L2_h1
import Theorems.Thm_ReciprocityTheory_PGsh_L2_h2
import Theorems.Thm_ReciprocityTheory_PGsh_Up_MulStable_const
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_succ_succ_alt
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_succ_zero_alt
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_zero_succ_alt
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_zero_zero_alt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_succ_succ_alt
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_succ_zero_alt
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_zero_succ_alt
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_zero_zero_alt


section
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.ChF
section Jets
open ReciprocityTheory.ChartRestriction.G.Chart GlobalTheory.ChartBaseChange GlobalTheory.ChartUniv
variable {R : Type} [CommRing R] {G : Over (Spec (CommRingCat.of R))} {κ : Type}
private theorem jetPt_indep (x : ∀ m, sp (R₀ := R) (JetR R κ m) ⟶ G)
    (ht : ∀ m, spMap (jetTruncR R κ m) ≫ x (m + 1) = x m) {S : Type} [CommRing S] [Algebra R S]
    {m m' : ℕ} (ψ : JetR R κ m →ₐ[R] S) (ψ' : JetR R κ m' →ₐ[R] S) (h : ∀ q, ψ (zR m q) = ψ' (zR m' q)) :
    spMap ψ ≫ x m = spMap ψ' ≫ x m' := by
  wlog hm : m ≤ m' generalizing m m'
  · exact (this ψ' ψ (fun q => (h q).symm) (by omega)).symm
  induction m', hm using Nat.le_induction with
  | base => rw [jet_ext h]
  | succ k hk ih =>
    let φ : JetR R κ k →ₐ[R] S :=
      ψ.comp (Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right (by omega)))
    have e : ψ' = φ.comp (jetTruncR R κ k) := jet_ext fun q => (h q).symm
    rw [ih φ (fun q => rfl), e, ← spMap_comp (jetTruncR R κ k), Category.assoc, ht]
private theorem exists_span_pow {ι' S : Type} [Finite ι'] [CommRing S] (b : ι' → S) (hb : ∀ i, IsNilpotent (b i)) :
    ∃ m : ℕ, Ideal.span (Set.range b) ^ (m + 1) = ⊥ := by
  have hfg : (Ideal.span (Set.range b)).FG := Submodule.fg_span (Set.finite_range b)
  obtain ⟨m, hm⟩ := hfg.isNilpotent_iff_le_nilradical.2 (Ideal.span_le.2 (by
    rintro _ ⟨i, rfl⟩
    exact hb i))
  exact ⟨m, by rw [pow_succ, hm, zero_mul, Ideal.zero_eq_bot]⟩
private theorem exists_jetHom_nil [Finite κ] {S : Type} [CommRing S] [Algebra R S] (b : κ → S)
    (hb : ∀ i, IsNilpotent (b i)) : ∃ (m : ℕ) (ψ : JetR R κ m →ₐ[R] S), ∀ q, ψ (zR m q) = b q := by
  obtain ⟨m, hm⟩ := exists_span_pow b hb
  exact ⟨m, jetLift R _ hm b (fun q => Ideal.subset_span ⟨q, rfl⟩), fun q => jetLift_zR _ _ _ _ q⟩
variable [GrpObj G]
private theorem aug_eq_one {m : ℕ} (x : sp (R₀ := R) (JetR R κ m) ⟶ G) (h0 : spMap (jetZeroR R κ m) ≫ x = 1) :
    spMap (jetAug R κ m) ≫ x = 1 := by
  rw [jetAug_eq, ← spMap_comp, Category.assoc, h0, MonObj.comp_one]
variable [IsLocalRing R] [Smooth G.hom] {m : ℕ} (x : sp (R₀ := R) (JetR R κ m) ⟶ G)
  (h0 : spMap (jetZeroR R κ m) ≫ x = 1)
  (hu : ∀ (κ' : Type) (y : sp (R₀ := R) (JetR R κ' m) ⟶ G), spMap (jetZeroR R κ' m) ≫ y = 1 →
    ∃! ψ : JetR R κ m →ₐ[R] JetR R κ' m, (∀ j, jetZeroR R κ' m (ψ (zR m j)) = 0) ∧ y = spMap ψ ≫ x)
  {A B : Type} [CommRing A] [Algebra R A] [CommRing B] [Algebra R B] (q : A →ₐ[R] B)
  (hJ : (RingHom.ker q) ^ (m + 1) = ⊥)
include h0 hu hJ in
private theorem jetPt_surj (hq : Function.Surjective q) (y : sp (R₀ := R) A ⟶ G) (hy : spMap q ≫ y = 1) :
    ∃ ψ : JetR R κ m →ₐ[R] A, (∀ j, q (ψ (zR m j)) = 0) ∧ y = spMap ψ ≫ x := by
  obtain ⟨C⟩ := exists_chart G
  obtain ⟨h, hh, hqh⟩ := exists_pt_of_aug C q hq hJ y hy
  obtain ⟨ψ₀, ⟨ha, hψ₀⟩, -⟩ := univ_all x h0 hu (fib q) (fibFst q) (fib_ker q hJ)
    (pt C (fibLift q (eps C) h hqh)) (by rw [spMap_pt]; exact pt_eps_self C)
  refine ⟨(fibSnd q).comp ψ₀, fun j => ?_, ?_⟩
  · rw [AlgHom.comp_apply, fib_cond,
      show fibFst q (ψ₀ (zR m j)) = 0 from (AlgHom.congr_fun ha _).trans (jetAug_zR m j), map_zero]
  · rw [← spMap_comp, Category.assoc, ← hψ₀, spMap_pt, hh]
    rfl
include h0 hu hJ in
private theorem jetPt_inj (ψ ψ' : JetR R κ m →ₐ[R] A) (hψ : ∀ j, q (ψ (zR m j)) = 0)
    (hψ' : ∀ j, q (ψ' (zR m j)) = 0) (e : spMap ψ ≫ x = spMap ψ' ≫ x) : ψ = ψ' := by
  obtain ⟨C⟩ := exists_chart G
  obtain ⟨k, hk, -⟩ := exists_pt_of_aug C (jetAug R κ m) (fun r => ⟨algebraMap _ _ r, AlgHom.commutes _ r⟩)
    (ker_jetAug_pow _ m) x (aug_eq_one x h0)
  have hv : ∀ v : JetR R κ m →ₐ[R] A, (∀ j, q (v (zR m j)) = 0) →
      q.comp v = (Algebra.ofId R B).comp (jetAug R κ m) := fun v hv =>
    jet_ext fun j => by rw [AlgHom.comp_apply, AlgHom.comp_apply, hv, jetAug_zR, map_zero]
  have e1 : ψ.comp k = ψ'.comp k := by
    apply pt_injective C
    rw [← spMap_pt, ← spMap_pt, ← hk, e]
  have e2 : fibLift q (jetAug R κ m) ψ (hv ψ hψ) = fibLift q (jetAug R κ m) ψ' (hv ψ' hψ') := by
    refine (univ_all x h0 hu (fib q) (fibFst q) (fib_ker q hJ)
      (spMap (fibLift q (jetAug R κ m) ψ (hv ψ hψ)) ≫ x) ?_).unique ⟨rfl, rfl⟩ ⟨rfl, ?_⟩
    · rw [← Category.assoc, spMap_comp]
      exact aug_eq_one x h0
    · rw [hk, spMap_pt, spMap_pt]
      congr 1
      exact AlgHom.ext fun s => Subtype.ext (Prod.ext rfl (AlgHom.congr_fun e1 s))
  exact AlgHom.ext fun s => congrArg (fibSnd q) (AlgHom.congr_fun e2 s)
end Jets
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
private theorem psJet_eq_nv {R : Type} [CommRing R] {n d : ℕ} (m : ℕ) (f : PS R n d)
    (hf : MvPowerSeries.constantCoeff f = 0) :
    psJet m f = nv (algebraMap R (Chart.JetR R (Fin n × Fin d) m)) f (fun i j => Chart.zR m (i, j)) := by
  classical
  have hz : ∀ q : Fin n × Fin d, (Chart.zR (R := R) m q) ^ (m + 1) = 0 := fun q => by
    have := Ideal.pow_mem_pow (Chart.zR_mem_ker (R := R) m q) (m + 1)
    rwa [Chart.ker_jetAug_pow, Ideal.mem_bot] at this
  have h1 : nv (algebraMap R (Chart.JetR R (Fin n × Fin d) m)) f (fun i j => Chart.zR m (i, j)) =
      ∑ e : Fin n × Fin d → Fin (m + 1), algebraMap R (Chart.JetR R (Fin n × Fin d) m) (MvPowerSeries.coeff
      (Finsupp.equivFunOnFinite.symm fun i => (e i : ℕ)) f) * ∏ i, (Chart.zR (R := R) m i) ^ (e i : ℕ) := by
    letI := (algebraMap R (Chart.JetR R (Fin n × Fin d) m)).toAlgebra
    exact evBasic_nEval_eq_tEval f (fun q : Fin n × Fin d => Chart.zR m q) (m + 1) hz
  have h2 : nv (algebraMap R (Chart.JetR R (Fin n × Fin d) m)) f (fun i j => Chart.zR m (i, j)) =
      Ideal.Quotient.mk _ (∑ e : Fin n × Fin d → Fin (m + 1), MvPolynomial.monomial
        (Finsupp.equivFunOnFinite.symm fun i => (e i : ℕ)) (MvPowerSeries.coeff
        (Finsupp.equivFunOnFinite.symm fun i => (e i : ℕ)) f)) := by
    rw [h1, map_sum]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [MvPolynomial.monomial_eq, Finsupp.prod_fintype _ _ (fun i => pow_zero _), map_mul, map_prod]
    simp only [map_pow]
    rfl
  rw [h2]
  refine (GlobalTheory.JetSer.jet_mk_eq_iff m _ _).2 fun e he => ?_
  have hle : ∀ i, e i < m + 1 := fun i => lt_of_le_of_lt (Finsupp.le_degree i e) he
  have hr : MvPolynomial.coeff e (∑ e : Fin n × Fin d → Fin (m + 1), MvPolynomial.monomial
        (Finsupp.equivFunOnFinite.symm fun i => (e i : ℕ)) (MvPowerSeries.coeff
        (Finsupp.equivFunOnFinite.symm fun i => (e i : ℕ)) f)) = MvPowerSeries.coeff e f := by
    have he0 : (Finsupp.equivFunOnFinite.symm fun i => ((⟨e i, hle i⟩ : Fin (m + 1)) : ℕ)) = e := by
      ext i; rfl
    rw [MvPolynomial.coeff_sum, Finset.sum_eq_single (fun i => (⟨e i, hle i⟩ : Fin (m + 1)))]
    · rw [he0, MvPolynomial.coeff_monomial, if_pos rfl]
    · intro e' _ hne
      rw [MvPolynomial.coeff_monomial, if_neg]
      intro h
      apply hne
      funext i
      exact Fin.ext (DFunLike.congr_fun h i)
    · intro h
      exact absurd (Finset.mem_univ _) h
  rw [hr, MvPowerSeries.coeff_trunc]
  split_ifs with hlt
  · rfl
  · by_cases h0 : e = 0
    · rw [h0, MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hf]
    · exfalso
      apply hlt
      obtain ⟨i, -⟩ := Finsupp.ne_iff.1 h0
      exact lt_of_le_of_ne (fun j => (hle j).le) fun h => (hle i).ne (DFunLike.congr_fun h i)
private theorem map_psJet {R S : Type} [CommRing R] [CommRing S] [Algebra R S] {n d m : ℕ}
    (φ : Chart.JetR R (Fin n × Fin d) m →ₐ[R] S) (a : Fin n → Fin d → S)
    (ha : ∀ q, φ (Chart.zR m q) = a q.1 q.2) (f : PS R n d) (hf : MvPowerSeries.constantCoeff f = 0) :
    φ (psJet m f) = nv (algebraMap R S) f a := by
  have hn : ∀ i j, IsNilpotent (Chart.zR (R := R) m ((i, j) : Fin n × Fin d)) := fun i j => ⟨m + 1, by
    have := Ideal.pow_mem_pow (Chart.zR_mem_ker (R := R) m ((i, j) : Fin n × Fin d)) (m + 1)
    rwa [Chart.ker_jetAug_pow, Ideal.mem_bot] at this⟩
  have h := (nv_calculus R _ (algebraMap R (Chart.JetR R (Fin n × Fin d) m)) n d
    (fun i j => Chart.zR m (i, j)) hn).2.2.2.2.1 S (φ : _ →+* S) f
  rw [psJet_eq_nv m f hf]
  refine h.trans ?_
  rw [φ.comp_algebraMap]
  congr 1
  funext i j
  exact ha (i, j)
private theorem map_substJ {R S : Type} [CommRing R] [CommRing S] [Algebra R S] {n d m : ℕ}
    (φ : Chart.JetR R (Fin n × Fin d) m →ₐ[R] S) (a : Fin n → Fin d → S)
    (ha : ∀ q, φ (Chart.zR m q) = a q.1 q.2) (f : Fin d → PS R n d)
    (hf : ∀ j, MvPowerSeries.constantCoeff (f j) = 0) (q : Fin 1 × Fin d) :
    φ.comp (substJ m f hf) (Chart.zR m q) = nv (algebraMap R S) (f q.2) a := by
  rw [← map_psJet φ a ha _ (hf q.2), AlgHom.comp_apply]
  congr 1
  exact MvPolynomial.aeval_X _ q
end GlobalTheory.ChF
end
end

set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
namespace GlobalTheory.ChF
theorem _root_.solution : ∀ (R : Type) [CommRing R] [IsLocalRing R] (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G], Smooth G.hom → ∀ (d : ℕ) (F : FGLaw R d) (x : ∀ m : ℕ, Geo.Tor.algOver R (Geo.Tor.JetR R (Fin 1 × Fin d) m) ⟶ G), IsChartJ G F x → ∃ X : Fam G d, NilChart G F.F X ∧ ∀ (OE : Type) [CommRing OE] (io : Out.RingAct G OE) (act : Geo.Tor.Germ.OAct OE F), ChartActs G x io act → ∀ a, Reads X X (io.act a) (act.act a) := by
  intro R _ _ G _ _ hG d F x₀ hx
  classical
  haveI := hG
  let x : ∀ m, sp (R₀ := R) (Chart.JetR R (Fin 1 × Fin d) m) ⟶ G := x₀
  have ht : ∀ m, spMap (Chart.jetTruncR R _ m) ≫ x (m + 1) = x m := hx.trunc
  have h0 : ∀ m, spMap (Chart.jetZeroR R _ m) ≫ x m = 1 := hx.zero
  have hl : ∀ m, spMap (substJ m F.F F.const) ≫ x m =
      (spMap (jetPt (d := d) (0 : Fin 2) m) ≫ x m) * (spMap (jetPt (d := d) (1 : Fin 2) m) ≫ x m) := hx.law
  obtain ⟨X, hX⟩ : ∃ X : Fam G d, ∀ (S : Type) [CommRing S] [Algebra R S] (a : Fin d → S) (m : ℕ)
      (ψ : Chart.JetR R (Fin 1 × Fin d) m →ₐ[R] S), (∀ q, ψ (Chart.zR m q) = a q.2) →
      X S a = spMap ψ ≫ x m := by
    refine ⟨fun S _ _ a => if h : ∃ (m : ℕ) (ψ : Chart.JetR R (Fin 1 × Fin d) m →ₐ[R] S),
      ∀ q, ψ (Chart.zR m q) = a q.2 then spMap h.choose_spec.choose ≫ x h.choose else 1, ?_⟩
    intro S _ _ a m ψ hψ
    have h : ∃ (m : ℕ) (ψ : Chart.JetR R (Fin 1 × Fin d) m →ₐ[R] S), ∀ q, ψ (Chart.zR m q) = a q.2 :=
      ⟨m, ψ, hψ⟩
    exact (dif_pos h).trans
      (jetPt_indep x ht _ ψ fun q => (h.choose_spec.choose_spec q).trans (hψ q).symm)
  refine ⟨X, ⟨fun S _ _ => ?_, fun S _ _ S' _ _ φ a ha => ?_, fun S _ _ a b ha hb e => ?_,
    fun S _ _ S' _ _ ρ σ hρ hn z hz => ?_, fun S _ _ a b ha hb => ?_⟩,
    fun OE _ io act hact c => ⟨act.const c, fun S _ _ a ha => ?_⟩⟩
  · rw [hX S 0 0 ((Algebra.ofId R S).comp (Chart.jetAug R _ 0)) (fun q => by
      rw [AlgHom.comp_apply, Chart.jetAug_zR, map_zero]; rfl), ← Chart.spMap_comp, Category.assoc,
      aug_eq_one (x 0) (h0 0), MonObj.comp_one]
  · obtain ⟨m, ψ, hψ⟩ := exists_jetHom_nil (R := R) (fun q : Fin 1 × Fin d => a q.2) fun q => ha _
    rw [hX S a m ψ hψ, hX S' (fun i => φ (a i)) m (φ.comp ψ) (fun q => congrArg φ (hψ q)), ← Category.assoc, Chart.spMap_comp]
  · obtain ⟨m, hm⟩ := exists_span_pow (Sum.elim a b) (by rintro (i | i); exacts [ha i, hb i])
    let J := Ideal.span (Set.range (Sum.elim a b))
    have hJa : ∀ q : Fin 1 × Fin d, a q.2 ∈ J := fun q => Ideal.subset_span ⟨Sum.inl q.2, rfl⟩
    have hJb : ∀ q : Fin 1 × Fin d, b q.2 ∈ J := fun q => Ideal.subset_span ⟨Sum.inr q.2, rfl⟩
    have ea := Chart.jetLift_zR (R := R) J hm _ hJa
    have eb := Chart.jetLift_zR (R := R) J hm _ hJb
    rw [hX S a m _ ea, hX S b m _ eb] at e
    have hk : RingHom.ker (Ideal.Quotient.mkₐ R J) = J := Ideal.mk_ker
    have := jetPt_inj (x m) (h0 m) (fun κ' => hx.univ κ' m) (Ideal.Quotient.mkₐ R J) (by rw [hk]; exact hm) _ _
      (fun q => by rw [ea]; exact Ideal.Quotient.eq_zero_iff_mem.2 (hJa q))
      (fun q => by rw [eb]; exact Ideal.Quotient.eq_zero_iff_mem.2 (hJb q)) e
    funext i
    exact (ea (0, i)).symm.trans (this ▸ eb (0, i))
  · obtain ⟨m, hm⟩ := hn
    have hm' : RingHom.ker ρ ^ (m + 1) = ⊥ := by rw [pow_succ, hm, zero_mul, Ideal.zero_eq_bot]
    obtain ⟨ψ, h1, h2⟩ := jetPt_surj (x m) (h0 m) (fun κ' => hx.univ κ' m) ρ hm'
      (fun s => ⟨σ s, AlgHom.congr_fun hρ s⟩) z hz
    refine ⟨fun i => ψ (Chart.zR m (0, i)), fun i => h1 _, h2.trans (hX S _ m ψ ?_).symm⟩
    rintro ⟨i, j⟩
    rw [Subsingleton.elim i 0]
  · have hab : ∀ i j, IsNilpotent ((![a, b] : Fin 2 → Fin d → S) i j) := fun i j => by
      fin_cases i
      exacts [ha j, hb j]
    obtain ⟨m, φ, hφ⟩ := exists_jetHom_nil (R := R)
      (fun q : Fin 2 × Fin d => (![a, b] : Fin 2 → Fin d → S) q.1 q.2) fun q => hab _ _
    obtain ⟨ψ, hψ, -, hψX⟩ := (nv_calculus R S (algebraMap R S) 2 d ![a, b] hab).1
    have hp : ∀ (i : Fin 2) (q : Fin 1 × Fin d), φ.comp (jetPt (d := d) i m) (Chart.zR m q) =
        (![a, b] : Fin 2 → Fin d → S) i q.2 := fun i q =>
      (map_substJ φ _ hφ _ _ q).trans ((hψ _).symm.trans (hψX (i, q.2)))
    rw [hX S a m _ (hp 0), hX S b m _ (hp 1), hX S _ m _ (map_substJ φ _ hφ F.F F.const),
      ← Chart.spMap_comp, ← Chart.spMap_comp, ← Chart.spMap_comp, Category.assoc, Category.assoc,
      Category.assoc, hl, MonObj.comp_mul]
  · obtain ⟨m, φ, hφ⟩ := exists_jetHom_nil (R := R) (fun q : Fin 1 × Fin d => a q.2) fun q => ha _
    have hφ' : ∀ q : Fin 1 × Fin d, φ (Chart.zR m q) = (![a] : Fin 1 → Fin d → S) q.1 q.2 := by
      rintro ⟨i, j⟩
      rw [hφ, Subsingleton.elim i 0]
      rfl
    have hc : x m ≫ io.act c = spMap (substJ m (act.act c) (act.const c)) ≫ x m := hact m c
    rw [hX S a m φ hφ, hX S _ m _ (map_substJ φ _ hφ' (act.act c) (act.const c)),
      ← Chart.spMap_comp, Category.assoc, Category.assoc, hc]
end GlobalTheory.ChF
