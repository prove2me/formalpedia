-- Prove2me | solution 1 for OAI.MaximalSeshadri.NodalLocal.nodal_associated_quadrilateral_s01
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T15:17:10.199198+00:00
-- url     : https://prove2.me/submissions/bcefa999-a74e-4fa8-9c80-76c73344682b

import Mathlib
import Definitions.Def_Q223SES003
import Definitions.Def_Q223SES005

section
-- module Solutions.Q223_SES.Seshadri_Lattice_InitialWeights
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.Geometry.schemeHasExt _root_.OAI.MaximalSeshadri.Geometry.sheafHomModule _root_.OAI.MaximalSeshadri.Geometry.sheafLinear _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms
attribute [-simp] _root_.OAI.MaximalSeshadri.AnalyticCoordinates.biCoeff_biSeries
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                            
section

namespace MaximalSeshadri
open scoped BigOperators Topology
open Filter Set

lemma finite_boundedWeight (t M : ℝ) (ht : 0 < t) :
    {p : Exponent | exponentWeight t p < M}.Finite := by
  refine (Set.finite_Iic (⟨⌈M⌉₊, ⌈M / t⌉₊⟩ : Exponent)).subset ?_
  intro p hp
  change p.1 ≤ ⌈M⌉₊ ∧ p.2 ≤ ⌈M / t⌉₊
  have hp' : (p.1 : ℝ) + t * p.2 < M := hp
  have h1 : (p.1 : ℝ) ≤ M := by nlinarith [Nat.cast_nonneg (α := ℝ) p.2]
  have h2 : (p.2 : ℝ) ≤ M / t := by
    apply (le_div_iff₀ ht).mpr
    nlinarith [Nat.cast_nonneg (α := ℝ) p.1]
  exact ⟨(Nat.cast_le (α := ℝ)).mp (h1.trans (Nat.le_ceil M)),
    (Nat.cast_le (α := ℝ)).mp (h2.trans (Nat.le_ceil (M / t)))⟩

lemma lexKey_le_iff (t : ℝ) (p q : Exponent) :
    lexKey t p ≤ lexKey t q ↔ exponentWeight t p ≤ exponentWeight t q ∧
      (exponentWeight t p = exponentWeight t q → p.2 ≤ q.2) :=
  Prod.Lex.toLex_le_toLex'

lemma lexKey_injective (t : ℝ) : Function.Injective (lexKey t) := by
  intro p q h
  have hy : p.2 = q.2 := congrArg (fun z : ℝ ×ₗ ℕ => (ofLex z).2) h
  have hw : exponentWeight t p = exponentWeight t q :=
    congrArg (fun z : ℝ ×ₗ ℕ => (ofLex z).1) h
  apply Prod.ext
  · have hα : (p.1 : ℝ) = q.1 := by simpa [exponentWeight, hy] using hw
    exact Nat.cast_inj.mp hα
  · exact hy

lemma LexInitial.key_le {c : Exponent → ℂ} {t : ℝ} {e : Exponent}
    (h : LexInitial c t e) {p : Exponent} (hp : c p ≠ 0) :
    lexKey t e ≤ lexKey t p := (lexKey_le_iff t e p).mpr (h.2 p hp)

lemma LexInitial.unique {c : Exponent → ℂ} {t : ℝ} {e f : Exponent}
    (he : LexInitial c t e) (hf : LexInitial c t f) : e = f :=
  lexKey_injective t (le_antisymm (he.key_le hf.1) (hf.key_le he.1))

theorem exists_lexInitial (c : Exponent → ℂ) (t : ℝ) (ht : 0 < t)
    (hc : c ≠ 0) : ∃ e, LexInitial c t e := by
  classical
  obtain ⟨p, hp⟩ : ∃ p, c p ≠ 0 := by
    by_contra! h
    exact hc (funext h)
  let B : Set Exponent := {q | c q ≠ 0 ∧ exponentWeight t q < exponentWeight t p + 1}
  have hB : B.Finite :=
    (finite_boundedWeight t (exponentWeight t p + 1) ht).subset fun _ h => h.2
  have hpB : p ∈ B := ⟨hp, lt_add_one _⟩
  obtain ⟨e, heB, he⟩ := Set.exists_min_image B (lexKey t) hB ⟨p, hpB⟩
  refine ⟨e, heB.1, fun q hq => (lexKey_le_iff t e q).mp ?_⟩
  by_cases hqB : q ∈ B
  · exact he q hqB
  · have hqp : exponentWeight t p + 1 ≤ exponentWeight t q := by
      by_contra! h
      exact hqB ⟨hq, h⟩
    have hep := ((lexKey_le_iff t e p).mp (he p hpB)).1
    apply Prod.Lex.toLex_le_toLex.mpr
    exact Or.inl (by dsimp [lexKey] <;> linarith)

end MaximalSeshadri


end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Nodal_NodalIntersection
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.jetIndexFinite _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.Geometry.schemeHasExt _root_.OAI.MaximalSeshadri.Geometry.sheafHomModule _root_.OAI.MaximalSeshadri.Geometry.sheafLinear _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
                                           
section

namespace MaximalSeshadri
namespace NodalLocal

open PowerSeries

noncomputable section

variable (K : Type*) [Field K]

theorem range_includeX_eq_ker_branchZ :
    (includeX K).range = (branchZ K).toLinearMap.ker := by
  ext f
  constructor
  · rintro ⟨g, rfl⟩
    simp
  · intro hf
    have hz : branchZ K f = 0 := hf
    have hx : constantCoeff (branchX K f) = 0 := by rw [branch_constant, hz, map_zero]
    obtain ⟨g, hg⟩ := PowerSeries.X_dvd_iff.mpr hx
    refine ⟨g, ?_⟩
    apply node_ext <;> simp [hg, hz]

lemma finite_branch_quotient (f : PowerSeries K) (hf : f ≠ 0) :
    FiniteDimensional K (PowerSeries K ⧸ multiples K f) :=
  FiniteDimensional.of_injective (branchQuotientEquiv K f hf).toLinearMap
    (branchQuotientEquiv K f hf).injective

lemma finrank_branch_quotient (f : PowerSeries K) (hf : f ≠ 0) :
    Module.finrank K (PowerSeries K ⧸ multiples K f) = f.order.toNat := by
  rw [(branchQuotientEquiv K f hf).finrank_eq, Module.finrank_pi]
  simp

lemma quotientZ_surjective (f : Node K) : Function.Surjective (quotientZ K f) := by
  intro q
  induction q using Submodule.Quotient.induction_on with
  | H g =>
    exact ⟨Submodule.Quotient.mk (liftZ K g), by simp⟩

lemma quotientX_injective (f : Node K) (hfz : branchZ K f ≠ 0) :
    Function.Injective (quotientX K f) := by
  rw [← LinearMap.ker_eq_bot]
  apply le_antisymm ?_ bot_le
  intro q hq
  change q = 0
  induction q using Submodule.Quotient.induction_on with
  | H h =>
    have hh : includeX K h ∈ multiples K f := by
      exact (Submodule.Quotient.mk_eq_zero _).mp hq
    obtain ⟨g, hg⟩ := (mem_multiples K f (includeX K h)).mp hh
    have hgz : branchZ K g = 0 := by
      have hz : branchZ K f * branchZ K g = 0 := by
        simpa using (congrArg (branchZ K) hg).symm
      exact (mul_eq_zero.mp hz).resolve_left hfz
    have hgc : constantCoeff (branchX K g) = 0 := by
      rw [branch_constant, hgz, map_zero]
    obtain ⟨a, ha⟩ := PowerSeries.X_dvd_iff.mpr hgc
    have hh' : h = branchX K f * a := by
      apply mul_left_cancel₀ (PowerSeries.X_ne_zero : (X : PowerSeries K) ≠ 0)
      calc
        X * h = branchX K f * branchX K g := by
          simpa using congrArg (branchX K) hg
        _ = X * (branchX K f * a) := by rw [ha]; ring
    change (Submodule.Quotient.mk h : PowerSeries K ⧸ multiples K (branchX K f)) = 0
    rw [Submodule.Quotient.mk_eq_zero, mem_multiples]
    exact ⟨a, hh'⟩

lemma branch_quotient_exact (f : Node K) :
    Function.Exact (quotientX K f) (quotientZ K f) := by
  rw [LinearMap.exact_iff]
  ext q
  constructor
  · intro hq
    induction q using Submodule.Quotient.induction_on with
    | H g =>
      have hg : branchZ K g ∈ multiples K (branchZ K f) := by
        exact (Submodule.Quotient.mk_eq_zero _).mp hq
      obtain ⟨b, hb⟩ := (mem_multiples K _ _).mp hg
      let g' := g - f * liftZ K b
      have hz : branchZ K g' = 0 := by simp [g', hb]
      have hmem : g' ∈ (includeX K).range := by
        rw [range_includeX_eq_ker_branchZ]
        exact hz
      obtain ⟨a, ha⟩ := hmem
      refine ⟨Submodule.Quotient.mk a, ?_⟩
      rw [quotientX_mk, Submodule.Quotient.eq]
      rw [ha]
      change g - f * liftZ K b - g ∈ multiples K f
      rw [show g - f * liftZ K b - g = f * (-liftZ K b) by ring]
      rw [mem_multiples]
      exact dvd_mul_right _ _
  · rintro ⟨a, rfl⟩
    induction a using Submodule.Quotient.induction_on with
    | H a =>
      change quotientZ K f (quotientX K f (Submodule.Quotient.mk a)) = 0
      simp

lemma finite_node_quotient (f : Node K)
    (hfx : branchX K f ≠ 0) (hfz : branchZ K f ≠ 0) :
    FiniteDimensional K (Node K ⧸ multiples K f) := by
  have := finite_branch_quotient K (branchX K f) hfx
  have := finite_branch_quotient K (branchZ K f) hfz
  exact Module.Finite.of_exact (branch_quotient_exact K f) (quotientZ_surjective K f)

theorem finrank_node_quotient (f : Node K)
    (hfx : branchX K f ≠ 0) (hfz : branchZ K f ≠ 0) :
    Module.finrank K (Node K ⧸ multiples K f) =
      (branchX K f).order.toNat + (branchZ K f).order.toNat := by
  have := finite_node_quotient K f hfx hfz
  have hex := LinearMap.exact_iff.mp (branch_quotient_exact K f)
  have hs : (quotientZ K f).range = ⊤ :=
    LinearMap.range_eq_top.mpr (quotientZ_surjective K f)
  have h := (quotientZ K f).finrank_range_add_finrank_ker
  rw [hs, finrank_top, hex,
    LinearMap.finrank_range_of_inj (quotientX_injective K f hfz),
    finrank_branch_quotient K _ hfz, finrank_branch_quotient K _ hfx] at h
  omega

theorem nodal_intersection_colength (f : Bivariate K)
    (hx : restrictX K f ≠ 0) (hz : restrictZ K f ≠ 0) :
    Module.finrank K (Bivariate K ⧸ intersectionIdeal K f) =
      (restrictX K f).order.toNat + (restrictZ K f).order.toNat := by
  rw [(intersectionQuotientEquiv K f).finrank_eq]
  exact finrank_node_quotient K (toNode K f) hx hz

end

end NodalLocal
end MaximalSeshadri

end


end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Lattice_NodePolygon
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.Geometry.schemeHasExt _root_.OAI.MaximalSeshadri.Geometry.sheafHomModule _root_.OAI.MaximalSeshadri.Geometry.sheafLinear _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms
attribute [-simp] _root_.OAI.MaximalSeshadri.AnalyticCoordinates.biCoeff_biSeries
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MaximalSeshadri.NodalLocal
noncomputable section
open PowerSeries
open scoped BigOperators

lemma bivariateCoeff_x {K : Type*} [Field K] (f : Bivariate K) (n : ℕ) :
    bivariateCoeff f (n, 0) = coeff n (restrictX K f) := by
  simp [bivariateCoeff, coeff_zero_eq_constantCoeff_apply]

lemma bivariateCoeff_z {K : Type*} [Field K] (f : Bivariate K) (n : ℕ) :
    bivariateCoeff f (0, n) = coeff n (restrictZ K f) := by
  simp [bivariateCoeff, coeff_zero_eq_constantCoeff_apply]

theorem nodal_initial_weight_bound (f : Bivariate ℂ) (t : ℝ) (ht : 0 < t)
    (e : Exponent) (he : LexInitial (bivariateCoeff f) t e)
    (hx : restrictX ℂ f ≠ 0) (hz : restrictZ ℂ f ≠ 0) :
    exponentWeight t e * (1 + 1 / t) ≤
      (Module.finrank ℂ (Bivariate ℂ ⧸ intersectionIdeal ℂ f) : ℝ) := by
  have hx' : bivariateCoeff f ((restrictX ℂ f).order.toNat, 0) ≠ 0 := by
    rw [bivariateCoeff_x]
    exact PowerSeries.coeff_order hx
  have hz' : bivariateCoeff f (0, (restrictZ ℂ f).order.toNat) ≠ 0 := by
    rw [bivariateCoeff_z]
    exact PowerSeries.coeff_order hz
  have ha := (he.2 _ hx').1
  have hb := (he.2 _ hz').1
  simp only [exponentWeight, Nat.cast_zero, mul_zero, add_zero, zero_add] at ha hb
  have hc : exponentWeight t e / t ≤ ((restrictZ ℂ f).order.toNat : ℝ) := by
    apply (div_le_iff₀ ht).mpr
    simpa [exponentWeight, mul_comm] using hb
  rw [nodal_intersection_colength ℂ f hx hz, Nat.cast_add]
  dsimp [exponentWeight] at hc ⊢
  have heq : ((e.1 : ℝ) + t * e.2) * (1 + 1 / t) =
      ((e.1 : ℝ) + t * e.2) + ((e.1 : ℝ) + t * e.2) / t := by ring
  rw [heq]
  exact add_le_add ha hc

theorem residual_initial_weight_bound (f : Bivariate ℂ) (d H t n : ℝ)
    (ht : 0 < t) (e : Exponent) (he : LexInitial (bivariateCoeff f) t e)
    (hx : restrictX ℂ f ≠ 0) (hz : restrictZ ℂ f ≠ 0)
    (hcolength : (Module.finrank ℂ (Bivariate ℂ ⧸ intersectionIdeal ℂ f) : ℝ)
      ≤ n * d * H) :
    exponentWeight t e ≤ n * (d * H * t / (1 + t)) := by
  have h := (nodal_initial_weight_bound f t ht e he hx hz).trans hcolength
  have hden : 0 < 1 + t := by positivity
  rw [← mul_div_assoc]
  apply (le_div_iff₀ hden).mpr
  have hs : (1 + 1 / t) * t = 1 + t := by field_simp <;> ring
  calc
    exponentWeight t e * (1 + t) =
        (exponentWeight t e * (1 + 1 / t)) * t := by rw [mul_assoc, hs]
    _ ≤ (n * d * H) * t := mul_le_mul_of_nonneg_right h ht.le
    _ = n * (d * H * t) := by ring

lemma exponentWeight_add (t : ℝ) (p q : Exponent) :
    exponentWeight t (p + q) = exponentWeight t p + exponentWeight t q := by
  simp only [exponentWeight, Prod.fst_add, Prod.snd_add, Nat.cast_add]
  ring

lemma exponentWeight_pos (t : ℝ) (ht : 0 < t) (p : Exponent) (hp : p ≠ 0) :
    0 < exponentWeight t p := by
  by_cases hx : p.1 = 0
  · have hy : 0 < p.2 := by
      by_contra h
      apply hp
      exact Prod.ext hx (by change p.2 = 0; omega)
    simp only [exponentWeight, hx, Nat.cast_zero, zero_add]
    exact mul_pos ht (by exact_mod_cast hy)
  · have hx' : 0 < p.1 := Nat.pos_of_ne_zero hx
    exact add_pos_of_pos_of_nonneg (by exact_mod_cast hx')
      (mul_nonneg ht.le (Nat.cast_nonneg _))

lemma bivariateCoeff_mul (f g : Bivariate ℂ) (e : Exponent) :
    bivariateCoeff (f * g) e =
      ∑ q ∈ Finset.HasAntidiagonal.antidiagonal e.2, ∑ p ∈ Finset.HasAntidiagonal.antidiagonal e.1,
        bivariateCoeff f (p.1, q.1) * bivariateCoeff g (p.2, q.2) := by
  simp only [bivariateCoeff, PowerSeries.coeff_mul, map_sum]

lemma bivariateCoeff_eq_zero_of_weight_lt (f : Bivariate ℂ) (t : ℝ)
    (e p : Exponent) (he : LexInitial (bivariateCoeff f) t e)
    (hp : exponentWeight t p < exponentWeight t e) : bivariateCoeff f p = 0 := by
  by_contra h
  exact (not_lt_of_ge (he.2 p h).1) hp

lemma bivariateCoeff_eq_zero_of_proper_subterm (f : Bivariate ℂ) (t : ℝ) (ht : 0 < t)
    (e p q v : Exponent) (he : LexInitial (bivariateCoeff f) t e)
    (hs : p + q = v) (hp : p ≠ 0)
    (hv : exponentWeight t v ≤ exponentWeight t e) : bivariateCoeff f q = 0 := by
  apply bivariateCoeff_eq_zero_of_weight_lt f t e q he
  have hsum := congrArg (exponentWeight t) hs
  rw [exponentWeight_add] at hsum
  have hpos := exponentWeight_pos t ht p hp
  linarith

lemma bivariateCoeff_mul_of_weight_le (u f : Bivariate ℂ) (t : ℝ) (ht : 0 < t)
    (e v : Exponent) (he : LexInitial (bivariateCoeff f) t e)
    (hv : exponentWeight t v ≤ exponentWeight t e) :
    bivariateCoeff (u * f) v = bivariateCoeff u (0, 0) * bivariateCoeff f v := by
  classical
  rw [bivariateCoeff_mul]
  rw [Finset.sum_eq_single (0, v.2)]
  · rw [Finset.sum_eq_single (0, v.1)]
    · intro p hp hpne
      apply mul_eq_zero_of_right
      apply bivariateCoeff_eq_zero_of_proper_subterm f t ht e (p.1, 0) (p.2, v.2) v he
      · apply Prod.ext
        · exact Finset.HasAntidiagonal.mem_antidiagonal.mp hp
        · simp
      · intro h
        have hp1 : p.1 = 0 := congrArg Prod.fst h
        apply hpne
        apply Prod.ext hp1
        have hs := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
        omega
      · exact hv
    · intro h
      exact (h (by simp)).elim
  · intro q hq hqne
    apply Finset.sum_eq_zero
    intro p hp
    apply mul_eq_zero_of_right
    apply bivariateCoeff_eq_zero_of_proper_subterm f t ht e (p.1, q.1) (p.2, q.2) v he
    · exact Prod.ext (Finset.HasAntidiagonal.mem_antidiagonal.mp hp) (Finset.HasAntidiagonal.mem_antidiagonal.mp hq)
    · intro h
      have hq1 : q.1 = 0 := congrArg Prod.snd h
      apply hqne
      apply Prod.ext hq1
      have hs := Finset.HasAntidiagonal.mem_antidiagonal.mp hq
      omega
    · exact hv
  · intro h
    exact (h (by simp)).elim

theorem lexInitial_unit_mul (u f : Bivariate ℂ) (t : ℝ) (ht : 0 < t)
    (e : Exponent) (he : LexInitial (bivariateCoeff f) t e)
    (hu : bivariateCoeff u (0, 0) ≠ 0) :
    LexInitial (bivariateCoeff (u * f)) t e := by
  constructor
  · rw [bivariateCoeff_mul_of_weight_le u f t ht e e he le_rfl]
    exact mul_ne_zero hu he.1
  · intro v hv
    by_cases hle : exponentWeight t v ≤ exponentWeight t e
    · rw [bivariateCoeff_mul_of_weight_le u f t ht e v he hle] at hv
      exact he.2 v (right_ne_zero_of_mul hv)
    · exact ⟨(lt_of_not_ge hle).le, fun h => (hle h.symm.le).elim⟩

lemma bivariateCoeff_node_pow_mul (f : Bivariate ℂ) (j : ℕ) (v : Exponent) :
    bivariateCoeff (nodeEquation ℂ ^ j * f) v =
      if j ≤ v.1 ∧ j ≤ v.2 then bivariateCoeff f (v.1 - j, v.2 - j) else 0 := by
  have heq : nodeEquation ℂ ^ j * f =
      C ((X : PowerSeries ℂ) ^ j) * ((X : Bivariate ℂ) ^ j * f) := by
    rw [nodeEquation, mul_pow, ← map_pow, mul_assoc]
  rw [heq]
  simp only [bivariateCoeff, coeff_C_mul, coeff_X_pow_mul']
  by_cases hx : j ≤ v.1 <;> by_cases hz : j ≤ v.2 <;>
    simp [hx, hz]

lemma bivariateCoeff_node_pow_mul_add (f : Bivariate ℂ) (j : ℕ) (e : Exponent) :
    bivariateCoeff (nodeEquation ℂ ^ j * f) (e + (j, j)) = bivariateCoeff f e := by
  simp [bivariateCoeff_node_pow_mul]

theorem lexInitial_node_pow_mul (f : Bivariate ℂ) (j : ℕ) (t : ℝ)
    (e : Exponent) (he : LexInitial (bivariateCoeff f) t e) :
    LexInitial (bivariateCoeff (nodeEquation ℂ ^ j * f)) t (e + (j, j)) := by
  constructor
  · rw [bivariateCoeff_node_pow_mul_add]
    exact he.1
  · intro p hp
    have hpp : j ≤ p.1 ∧ j ≤ p.2 := by
      by_contra h
      rw [bivariateCoeff_node_pow_mul, ite_eq_right h] at hp
      exact hp rfl
    let q : Exponent := (p.1 - j, p.2 - j)
    have heqp : p = q + (j, j) := by
      apply Prod.ext <;> dsimp [q] <;> omega
    have hq : bivariateCoeff f q ≠ 0 := by
      simpa only [bivariateCoeff_node_pow_mul, ite_eq_left hpp] using hp
    obtain ⟨hw, hb⟩ := he.2 q hq
    constructor
    · rw [heqp, exponentWeight_add, exponentWeight_add]
      linarith
    · intro h
      rw [heqp, exponentWeight_add, exponentWeight_add] at h
      have hb' := hb (add_right_cancel h)
      simpa only [heqp, Prod.snd_add] using Nat.add_le_add_right hb' j

theorem lexInitial_nodal_factor (u f : Bivariate ℂ) (j : ℕ) (t : ℝ) (ht : 0 < t)
    (e : Exponent) (he : LexInitial (bivariateCoeff f) t e)
    (hu : bivariateCoeff u (0, 0) ≠ 0) :
    LexInitial (bivariateCoeff ((u * nodeEquation ℂ) ^ j * f)) t (e + (j, j)) := by
  have huj : bivariateCoeff (u ^ j) (0, 0) ≠ 0 := by
    simpa only [bivariateCoeff, coeff_zero_eq_constantCoeff_apply, map_pow] using
      pow_ne_zero j hu
  have hh := lexInitial_unit_mul (u ^ j) (nodeEquation ℂ ^ j * f) t ht (e + (j, j))
    (lexInitial_node_pow_mul f j t e he) huj
  simpa only [mul_pow, mul_assoc] using hh

end
end MaximalSeshadri.NodalLocal

namespace MaximalSeshadri
noncomputable section
open scoped BigOperators

theorem mem_nodeQuadrilateral_of_residual (a b c k x y j : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hk : 0 < k)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hj : 0 ≤ j)
    (h : x / a + y / b + j / c ≤ k) :
    (x + j, y + j) ∈ nodeQuadrilateral (k * a) (k * b) (k * c) := by
  let w : Fin 4 → ℝ := ![1 - (x / a + y / b + j / c) / k,
    x / (k * a), j / (k * c), y / (k * b)]
  let z : Fin 4 → ℝ × ℝ := ![(0, 0), (k * a, 0), (k * c, k * c), (0, k * b)]
  have hw : ∀ i ∈ (Finset.univ : Finset (Fin 4)), 0 ≤ w i := by
    intro i _
    fin_cases i
    · dsimp [w]
      have hh := (div_le_one hk).mpr h
      linarith
    · exact div_nonneg hx (mul_pos hk ha).le
    · exact div_nonneg hj (mul_pos hk hc).le
    · exact div_nonneg hy (mul_pos hk hb).le
  have hsum : ∑ i : Fin 4, w i = 1 := by
    simp only [Fin.sum_univ_four]
    dsimp [w]
    field_simp
    ring
  have hz : ∀ i ∈ (Finset.univ : Finset (Fin 4)), z i ∈
      nodeQuadrilateral (k * a) (k * b) (k * c) := by
    intro i _
    apply subset_convexHull ℝ _
    fin_cases i <;> simp [z]
  have hm := (convex_convexHull ℝ _).sum_mem hw hsum hz
  have heq : ∑ i : Fin 4, w i • z i = (x + j, y + j) := by
    simp only [Fin.sum_univ_four]
    apply Prod.ext <;> dsimp [w, z] <;> field_simp <;> ring
  rwa [heq] at hm

namespace NodalLocal

theorem nodal_factor_quadrilateral (u f : Bivariate ℂ) (j : ℕ)
    (d H t k n : ℝ) (hd : 0 < d) (hH : 0 < H) (ht : 0 < t) (hk : 0 < k)
    (e : Exponent) (he : LexInitial (bivariateCoeff f) t e)
    (hu : bivariateCoeff u (0, 0) ≠ 0)
    (hx : restrictX ℂ f ≠ 0) (hz : restrictZ ℂ f ≠ 0)
    (hcolength : (Module.finrank ℂ (Bivariate ℂ ⧸ intersectionIdeal ℂ f) : ℝ)
      ≤ n * d * H) (hdegree : n + (j : ℝ) * d = k) :
    ∀ p, LexInitial (bivariateCoeff ((u * nodeEquation ℂ) ^ j * f)) t p →
      ((p.1 : ℝ), (p.2 : ℝ)) ∈ nodeQuadrilateral
        (k * (d * H * t / (1 + t))) (k * (d * H / (1 + t))) (k / d) := by
  intro p hp
  have hpe := hp.unique (lexInitial_nodal_factor u f j t ht e he hu)
  subst p
  have hweight := residual_initial_weight_bound f d H t n ht e he hx hz hcolength
  have hden : 0 < 1 + t := by positivity
  have ha : 0 < d * H * t / (1 + t) := by positivity
  have hb : 0 < d * H / (1 + t) := by positivity
  have hres : (e.1 : ℝ) / (d * H * t / (1 + t)) +
      (e.2 : ℝ) / (d * H / (1 + t)) ≤ n := by
    have heq : (e.1 : ℝ) / (d * H * t / (1 + t)) +
        (e.2 : ℝ) / (d * H / (1 + t)) =
        exponentWeight t e / (d * H * t / (1 + t)) := by
      dsimp [exponentWeight]
      field_simp
    rw [heq]
    exact (div_le_iff₀ ha).mpr hweight
  have hh : (e.1 : ℝ) / (d * H * t / (1 + t)) +
      (e.2 : ℝ) / (d * H / (1 + t)) + (j : ℝ) / (1 / d) ≤ k := by
    simp only [div_div_eq_mul_div, div_one]
    linarith
  have hm := mem_nodeQuadrilateral_of_residual
    (d * H * t / (1 + t)) (d * H / (1 + t)) (1 / d) k e.1 e.2 j
    ha hb (by positivity) hk (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    (Nat.cast_nonneg _) hh
  simpa only [Prod.fst_add, Prod.snd_add, Nat.cast_add, mul_one_div] using hm

end NodalLocal
end
end MaximalSeshadri

end


end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Nodal_NodalAssociated
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.Geometry.schemeHasExt _root_.OAI.MaximalSeshadri.Geometry.sheafHomModule _root_.OAI.MaximalSeshadri.Geometry.sheafLinear _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms
attribute [-simp] _root_.OAI.MaximalSeshadri.AnalyticCoordinates.biCoeff_biSeries
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                         
section

namespace MaximalSeshadri.NodalLocal
noncomputable section
open PowerSeries

lemma bivariateCoeff_unit_ne_zero (u : Bivariate ℂ) (hu : IsUnit u) :
    bivariateCoeff u (0,0) ≠ 0 := by
  simpa only [bivariateCoeff,coeff_zero_eq_constantCoeff_apply,RingHom.comp_apply] using
    (hu.map ((constantCoeff : PowerSeries ℂ →+* ℂ).comp
      (constantCoeff : Bivariate ℂ →+* PowerSeries ℂ))).ne_zero

lemma lexInitial_associated {f g : Bivariate ℂ} (h : Associated f g)
    (t : ℝ) (ht : 0 < t) (e : Exponent) (he : LexInitial (bivariateCoeff f) t e) :
    LexInitial (bivariateCoeff g) t e := by
  obtain ⟨u,hu⟩ := h
  rw [← hu,mul_comm]
  exact lexInitial_unit_mul u f t ht e he (bivariateCoeff_unit_ne_zero u u.isUnit)

theorem nodal_associated_quadrilateral_s01_oai (u f g : Bivariate ℂ) (j : ℕ)
    (d H t k n : ℝ) (hd : 0 < d) (hH : 0 < H) (ht : 0 < t) (hk : 0 < k)
    (hu : IsUnit u) (hx : restrictX ℂ f ≠ 0) (hz : restrictZ ℂ f ≠ 0)
    (hcolength : (Module.finrank ℂ (Bivariate ℂ ⧸ intersectionIdeal ℂ f) : ℝ) ≤ n*d*H)
    (hdegree : n+(j:ℝ)*d=k) (hassoc : Associated ((u*nodeEquation ℂ)^j*f) g)
    (p : Exponent) (hp : LexInitial (bivariateCoeff g) t p) :
    ((p.1:ℝ),(p.2:ℝ)) ∈ nodeQuadrilateral
      (k*(d*H*t/(1+t))) (k*(d*H/(1+t))) (k/d) := by
  have hf : f ≠ 0 := fun h => hx (by rw [h,map_zero])
  have hc : bivariateCoeff f ≠ 0 := by
    intro h
    apply hf
    apply bivariateCoeffEquiv.injective
    change bivariateCoeff f = bivariateCoeff 0
    rw [h]
    funext p
    simp [bivariateCoeff]
  obtain ⟨e,he⟩ := exists_lexInitial _ t ht hc
  exact nodal_factor_quadrilateral u f j d H t k n hd hH ht hk e he
    (bivariateCoeff_unit_ne_zero u hu) hx hz hcolength hdegree p
    (lexInitial_associated hassoc.symm t ht p hp)
end
end MaximalSeshadri.NodalLocal

end



end OAI
end

theorem solution : type_of% @OAI.MaximalSeshadri.NodalLocal.nodal_associated_quadrilateral_s01_oai := @OAI.MaximalSeshadri.NodalLocal.nodal_associated_quadrilateral_s01_oai
