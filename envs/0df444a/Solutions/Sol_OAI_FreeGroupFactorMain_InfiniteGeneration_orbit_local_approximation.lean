-- Prove2me | solution 1 for OAI.FreeGroupFactorMain.InfiniteGeneration.orbit_local_approximation
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-11-04T03:40:59.790028+00:00
-- url     : https://prove2.me/submissions/f8ad72b5-6ac1-4ec1-8886-31a9c581ab2b

import Mathlib
import Definitions.Def_FreeGroupFactorProof18

set_option linter.all false

section
namespace OAI

noncomputable section

universe uG uH

open Set Metric Filter
open scoped NNReal Topology BigOperators ContDiff

namespace FreeGroupFactorMain

open scoped ENNReal

def rightRegular {G : Type uG} [Group G] (g : G) : GroupOperator G :=
  (hilbertReindex (Equiv.mulRight g⁻¹)).toContinuousLinearEquiv.toContinuousLinearMap

@[simp] theorem rightRegular_apply {G : Type uG} [Group G] (g : G)
    (ξ : GroupHilbert G) (h : G) : rightRegular g ξ h = ξ (h * g) := by
  simp [rightRegular]

@[simp] theorem rightRegular_star {G : Type uG} [Group G] (g : G) :
    star (rightRegular g) = rightRegular g⁻¹ := by
  change star ((hilbertReindex (Equiv.mulRight g⁻¹)) : GroupOperator G) = _
  rw [LinearIsometryEquiv.star_eq_symm]
  ext ξ b
  change ξ (b * g⁻¹) = rightRegular g⁻¹ ξ b
  rw [rightRegular_apply]

theorem left_right_commute {G : Type uG} [Group G] (g h : G) :
    leftRegular g * rightRegular h = rightRegular h * leftRegular g := by
  ext ξ b
  simp [mul_assoc]

theorem rightRegular_mem_commutant {G : Type uG} [Group G] (g : G) :
    rightRegular g ∈ StarSubalgebra.centralizer ℂ (leftTranslations G) := by
  rw [StarSubalgebra.mem_centralizer_iff, leftTranslations_eq_range]
  rintro _ ⟨h, rfl⟩
  exact ⟨left_right_commute h g, by simp only [leftRegular_star]; exact left_right_commute _ _⟩

theorem groupVN_commute_right {G : Type uG} [Group G] (T : groupVonNeumann G) (g : G) :
    rightRegular g * (T : GroupOperator G) = (T : GroupOperator G) * rightRegular g :=
  ((StarSubalgebra.mem_centralizer_iff ℂ).mp T.property _ (rightRegular_mem_commutant g)).1

theorem canonicalTrace_eq_inner {G : Type uG} [Group G] [DecidableEq G]
    (T : groupVonNeumann G) :
    canonicalTrace T = inner ℂ (lp.single 2 (1 : G) (1 : ℂ))
      ((T : GroupOperator G) (lp.single 2 (1 : G) (1 : ℂ))) := by
  classical
  simp only [canonicalTrace, lp.inner_single_left, RCLike.inner_apply, map_one, mul_one]
  apply congrArg (fun v : GroupHilbert G => ((T : GroupOperator G) v) 1)
  ext b
  simp [lp.single_apply, Pi.single_apply]

theorem canonicalTrace_star_mul {G : Type uG} [Group G] [DecidableEq G]
    (T : groupVonNeumann G) :
    canonicalTrace (star T * T) =
      (‖(T : GroupOperator G) (lp.single 2 (1 : G) (1 : ℂ))‖ ^ 2 : ℂ) := by
  rw [canonicalTrace_eq_inner]
  change inner ℂ (lp.single 2 (1 : G) (1 : ℂ))
    (star (T : GroupOperator G) ((T : GroupOperator G) (lp.single 2 (1 : G) (1 : ℂ)))) = _
  rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right]
  exact inner_self_eq_norm_sq_to_K _

end FreeGroupFactorMain

end

end OAI
end

section
namespace OAI

namespace FreeGroupFactorMain

noncomputable section

universe uG uH

open Set Metric Filter
open scoped NNReal Topology BigOperators ContDiff

open scoped ComplexConjugate

theorem deltaOne_eq {G : Type uG} [Group G] [DecidableEq G] :
    (deltaOne : GroupHilbert G) = lp.single 2 1 1 := by
  ext x
  simp [deltaOne, lp.single_apply, Pi.single_apply]

theorem groupVN_matrix {G : Type uG} [Group G] [DecidableEq G]
    (T : groupVonNeumann G) (x y : G) :
    ((T : GroupOperator G) (lp.single 2 y 1)) x =
      ((T : GroupOperator G) deltaOne) (x * y⁻¹) := by
  have hr : rightRegular y⁻¹ deltaOne = lp.single 2 y 1 := by
    ext b
    simp [deltaOne, lp.single_apply, Pi.single_apply, mul_inv_eq_one]
  rw [← hr]
  have hc := congrArg (fun f : GroupOperator G => f deltaOne)
    (groupVN_commute_right T y⁻¹)
  simpa only [mul_apply_eq_comp, rightRegular_apply] using
    congrArg (fun v : GroupHilbert G => v x) hc.symm

theorem groupVN_star_coefficient {G : Type uG} [Group G] [DecidableEq G]
    (T : groupVonNeumann G) (x : G) :
    ((star T : GroupOperator G) deltaOne) x =
      conj (((T : GroupOperator G) deltaOne) x⁻¹) := by
  calc
    ((star T : GroupOperator G) deltaOne) x =
        inner ℂ (lp.single 2 x (1 : ℂ)) ((star T : GroupOperator G) deltaOne) := by
      simp only [lp.inner_single_left, RCLike.inner_apply, map_one, mul_one]
    _ = inner ℂ ((T : GroupOperator G) (lp.single 2 x 1)) deltaOne := by
      exact ContinuousLinearMap.adjoint_inner_right _ _ _
    _ = conj (((T : GroupOperator G) (lp.single 2 x 1)) 1) := by
      simp only [deltaOne, lp.inner_single_right, RCLike.inner_apply, one_mul]
    _ = _ := by rw [groupVN_matrix]; simp

theorem canonicalTrace_star_mul_inner {G : Type uG} [Group G] [DecidableEq G]
    (T U : groupVonNeumann G) :
    canonicalTrace (star T * U) = inner ℂ
      ((T : GroupOperator G) deltaOne) ((U : GroupOperator G) deltaOne) := by
  classical
  rw [canonicalTrace_eq_inner, ← deltaOne_eq]
  change inner ℂ deltaOne (star (T : GroupOperator G) ((U : GroupOperator G) deltaOne)) = _
  rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right]

theorem canonicalTrace_mul {G : Type uG} [Group G] [DecidableEq G]
    (T U : groupVonNeumann G) : canonicalTrace (T * U) = canonicalTrace (U * T) := by
  have he (T U : groupVonNeumann G) :
      canonicalTrace (T * U) = ∑' x : G,
        ((T : GroupOperator G) deltaOne) x⁻¹ * ((U : GroupOperator G) deltaOne) x := by
    rw [← star_star T, canonicalTrace_star_mul_inner]
    change (∑' x, inner ℂ (((star T : GroupOperator G) deltaOne) x)
      (((U : GroupOperator G) deltaOne) x)) = _
    apply tsum_congr
    intro x
    rw [groupVN_star_coefficient]
    simp [RCLike.inner_apply, mul_comm]
  rw [he, he]
  simpa only [Equiv.inv_apply, inv_inv, mul_comm] using
    ((Equiv.inv G).tsum_eq (fun x =>
      ((T : GroupOperator G) deltaOne) x⁻¹ * ((U : GroupOperator G) deltaOne) x)).symm

open scoped ComplexConjugate ENNReal

open scoped ComplexConjugate

end

end FreeGroupFactorMain

end OAI
end

section
namespace OAI

namespace FreeGroupFactorMain

noncomputable section

universe uA uB uG uH uι

open Set Metric Filter
open scoped NNReal Topology BigOperators ContDiff

namespace UnitaryEvaluation
variable {A : Type uA} [CStarAlgebra A] {ι : Type uι}

end UnitaryEvaluation

section
open UnitaryEvaluation

variable {A : Type uA} {B : Type uB} [CStarAlgebra A] [CStarAlgebra B]

end
section

variable {A : Type uA} [CStarAlgebra A]

end

namespace UnitaryEvaluation
variable {A : Type uA} [CStarAlgebra A] {ι : Type uι} [Fintype ι] [DecidableEq ι]

end UnitaryEvaluation

section
open UnitaryEvaluation

variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

end

theorem twoNorm_sq {G : Type uG} [Group G] (T : groupVonNeumann G) :
    (twoNorm T : ℂ)^2 = canonicalTrace (star T*T) := by
  classical
  rw [canonicalTrace_star_mul, ← deltaOne_eq]
  rfl

theorem twoNorm_star {G : Type uG} [Group G] (T : groupVonNeumann G) :
    twoNorm (star T) = twoNorm T := by
  classical
  have hsq : (twoNorm (star T) : ℂ)^2 = (twoNorm T : ℂ)^2 := by
    rw [twoNorm_sq, twoNorm_sq, star_star]
    exact canonicalTrace_mul T (star T)
  have hr := congrArg Complex.re hsq
  norm_cast at hr
  nlinarith [norm_nonneg (groupL2 (star T)), norm_nonneg (groupL2 T)]

theorem twoNorm_mul_unitary_right {G : Type uG} [Group G]
    (U : unitary (groupVonNeumann G)) (T : groupVonNeumann G) :
    twoNorm (T*(U : groupVonNeumann G)) = twoNorm T := by
  rw [← twoNorm_star, star_mul]
  change twoNorm (((star U : unitary (groupVonNeumann G)) : groupVonNeumann G) * star T) = _
  rw [twoNorm_mul_unitary_left, twoNorm_star]

theorem twoNorm_iso {G : Type uG} {H : Type uH} [Group G] [Group H]
    (Φ : groupVonNeumann G ≃⋆ₐ[ℂ] groupVonNeumann H)
    (hΦ : ∀ T, canonicalTrace (Φ T) = canonicalTrace T) (T : groupVonNeumann G) :
    twoNorm (Φ T) = twoNorm T := by
  have hs : Φ (star T) = star (Φ T) := Φ.map_star' T
  have hm : Φ (star T * T) = Φ (star T) * Φ T := Φ.map_mul' (star T) T
  have hsq : (twoNorm (Φ T) : ℂ)^2 = (twoNorm T : ℂ)^2 := by
    rw [twoNorm_sq, twoNorm_sq, ← hs, ← hm, hΦ]
  have hr := congrArg Complex.re hsq
  norm_cast at hr
  nlinarith [norm_nonneg (groupL2 (Φ T)), norm_nonneg (groupL2 T)]

end

end FreeGroupFactorMain

end OAI
end

section
namespace OAI

noncomputable section

universe uG uH uι

open Set Metric Filter
open scoped NNReal Topology BigOperators ContDiff

namespace FreeGroupFactorMain
open scoped ENNReal

variable {G : Type uG} [Group G]

omit [Group G] in
theorem group_single_total [DecidableEq G] (K : Submodule ℂ (GroupHilbert G))
    (hK : IsClosed (K : Set (GroupHilbert G)))
    (hsingle : ∀ g : G, lp.single 2 g (1 : ℂ) ∈ K) : ⊤ ≤ K := by
  classical
  intro ξ _hξ
  have hs := lp.hasSum_single (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) ξ
  apply hK.mem_of_tendsto hs
  filter_upwards [] with s
  apply K.sum_mem
  intro g _hg
  have he : lp.single 2 g (ξ g) = (ξ g) • (lp.single 2 g (1 : ℂ) : GroupHilbert G) := by
    ext x
    simp [lp.single_apply, Pi.single_apply]
  rw [he]
  exact K.smul_mem _ (hsingle g)

variable {ι : Type uι}

end FreeGroupFactorMain

end

end OAI
end

section
namespace OAI

noncomputable section

universe uA uG uι

open Set Metric Filter
open scoped NNReal Topology BigOperators ContDiff

namespace FreeGroupFactorMain.Generation
variable {A : Type uA} [CStarAlgebra A] {ι : Type uι}

variable {G : Type uG} [Group G]

theorem twoNorm_add_le (x y : groupVonNeumann G) : twoNorm (x+y) ≤ twoNorm x + twoNorm y := by
  change ‖groupL2 (x+y)‖ ≤ _
  rw [map_add]
  exact norm_add_le _ _

theorem twoNorm_smul (c : ℂ) (x : groupVonNeumann G) : twoNorm (c • x) = ‖c‖ * twoNorm x := by
  change ‖groupL2 (c • x)‖ = _
  rw [map_smul, norm_smul]

theorem twoNorm_mul_sub_le (U V U' V' : unitary (groupVonNeumann G)) :
    twoNorm ((U : groupVonNeumann G)*(V : groupVonNeumann G)-
      (U' : groupVonNeumann G)*(V' : groupVonNeumann G)) ≤
      twoNorm ((U : groupVonNeumann G)-(U' : groupVonNeumann G)) +
      twoNorm ((V : groupVonNeumann G)-(V' : groupVonNeumann G)) := by
  have he : (U : groupVonNeumann G)*(V : groupVonNeumann G)-
      (U' : groupVonNeumann G)*(V' : groupVonNeumann G) =
      ((U : groupVonNeumann G)-(U' : groupVonNeumann G))*(V : groupVonNeumann G) +
      (U' : groupVonNeumann G)*((V : groupVonNeumann G)-(V' : groupVonNeumann G)) := by noncomm_ring
  rw [he]
  exact (twoNorm_add_le _ _).trans_eq (by rw [twoNorm_mul_unitary_right, twoNorm_mul_unitary_left])

end FreeGroupFactorMain.Generation

namespace FreeGroupFactorMain
open UnitaryEvaluation

end FreeGroupFactorMain

end

end OAI
end

section
namespace OAI

noncomputable section

universe uA uB uC uG uH uI uK uP uX uY uι uκ

open Set Metric Filter
open scoped NNReal Topology BigOperators ContDiff

namespace FreeGroupFactorMain.Generation

section
variable {A : Type uA} {B : Type uB} [CStarAlgebra A] [CStarAlgebra B] {ι : Type uι} {κ : Type uκ}

def substitute (w : κ → FreeGroup ι) : (FreeGroup κ →₀ ℂ) →ₗ[ℂ] FreeGroup ι →₀ ℂ :=
  Finsupp.lmapDomain ℂ ℂ (FreeGroup.lift w)

@[simp] theorem poly_substitute (U : ι → unitary A) (w : κ → FreeGroup ι) (p : FreeGroup κ →₀ ℂ) :
    poly U (substitute w p) = poly (wordTuple U w) p := by
  induction p using Finsupp.induction_linear with
  | zero => simp only [map_zero,poly_zero]
  | add p q hp hq => simp only [map_add,poly_add,hp,hq]
  | single g c =>
    simp only [substitute,Finsupp.lmapDomain_apply,Finsupp.mapDomain_single,poly_single,word_wordTuple]

end

theorem canonical_poly_dense {ι : Type uι} (ξ : GroupHilbert (FreeGroup ι)) {ε : ℝ} (hε : 0 < ε) :
    ∃ p : FreeGroup ι →₀ ℂ, ‖groupL2 (poly generatorUnitary p)-ξ‖ < ε := by
  classical
  let K := Submodule.span ℂ (Set.range (fun g : FreeGroup ι => groupL2 (groupUnitary g)))
  have ht : ⊤ ≤ K.topologicalClosure := by
    apply group_single_total _ (Submodule.isClosed_topologicalClosure _)
    intro g
    rw [← groupL2_groupUnitary g]
    exact Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨g,rfl⟩)
  have hx : ξ ∈ closure (K : Set (GroupHilbert (FreeGroup ι))) := by
    rw [← Submodule.topologicalClosure_coe]
    exact ht trivial
  obtain ⟨x,hx,hd⟩ := Metric.mem_closure_iff.mp hx ε hε
  obtain ⟨p,hp⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hx
  refine ⟨p,?_⟩
  have he : groupL2 (poly generatorUnitary p) = x := by
    rw [poly,Finsupp.sum]
    simp only [map_sum,map_smul,word_canonical]
    exact hp
  rw [he,← dist_eq_norm,dist_comm]
  exact hd

theorem automorphism_poly_dense {ι : Type uι}
    (Φ : groupVonNeumann (FreeGroup ι) ≃⋆ₐ[ℂ] groupVonNeumann (FreeGroup ι))
    (ht : ∀ T, canonicalTrace (Φ T) = canonicalTrace T)
    (T : groupVonNeumann (FreeGroup ι)) {ε : ℝ} (hε : 0 < ε) :
    ∃ p : FreeGroup ι →₀ ℂ, twoNorm (poly (mapTuple Φ generatorUnitary) p-T) < ε := by
  obtain ⟨p,hp⟩ := canonical_poly_dense (groupL2 (Φ.symm T)) hε
  refine ⟨p,?_⟩
  rw [poly_mapTuple,← Φ.apply_symm_apply T,← map_sub,twoNorm_iso Φ ht]
  change ‖groupL2 (poly generatorUnitary p-Φ.symm T)‖ < ε
  rw [map_sub]
  exact hp

end FreeGroupFactorMain.Generation

namespace FreeGroupFactorMain

open Generation

end FreeGroupFactorMain

end

end OAI
end

section
namespace OAI

noncomputable section

universe uA uG uι

open Set Metric Filter
open scoped NNReal Topology BigOperators ContDiff ENNReal

attribute [local instance] Classical.propDecidable

namespace FreeGroupFactorMain.Generation

end FreeGroupFactorMain.Generation

namespace FreeGroupFactorMain.InfiniteGeneration
open Generation

end FreeGroupFactorMain.InfiniteGeneration

namespace FreeGroupFactorMain.Generation
variable {G : Type uG} [Group G] {ι : Type uι}

theorem word_twoNorm_finite_bound (g : FreeGroup ι) :
    ∃ (s : Finset ι) (K : ℝ), 0 ≤ K ∧
      ∀ (U V : ι → unitary (groupVonNeumann G)) (δ : ℝ), 0 ≤ δ →
        (∀ j ∈ s, twoNorm ((U j : groupVonNeumann G)-(V j : groupVonNeumann G)) ≤ δ) →
        twoNorm (word U g-word V g) ≤ K*δ := by
  classical
  induction g using FreeGroup.induction_on with
  | C1 =>
    refine ⟨∅,0,le_rfl,?_⟩
    intro U V δ _hδ _hUV
    simp only [map_one,sub_self,twoNorm_zero,zero_mul,le_refl]
  | of j =>
    refine ⟨{j},1,by norm_num,?_⟩
    intro U V δ _hδ hUV
    simpa only [word_of,one_mul] using hUV j (Finset.mem_singleton_self j)
  | inv_of j ih =>
    obtain ⟨s,K,hK,hb⟩ := ih
    refine ⟨s,K,hK,?_⟩
    intro U V δ hδ hUV
    rw [word_inv,word_inv,← star_sub,twoNorm_star]
    exact hb U V δ hδ hUV
  | mul g h hg hh =>
    obtain ⟨s,K,hK,hb⟩ := hg
    obtain ⟨t,L,hL,hl⟩ := hh
    refine ⟨s ∪ t,K+L,add_nonneg hK hL,?_⟩
    intro U V δ hδ hUV
    rw [map_mul,map_mul]
    exact (twoNorm_mul_sub_le (FreeGroup.lift U g) (FreeGroup.lift U h)
      (FreeGroup.lift V g) (FreeGroup.lift V h)).trans (by
      simpa only [add_mul,word,MonoidHom.comp_apply,Submonoid.subtype_apply] using
        add_le_add (hb U V δ hδ (fun j hj => hUV j (Finset.mem_union_left _ hj)))
          (hl U V δ hδ (fun j hj => hUV j (Finset.mem_union_right _ hj))))

theorem poly_twoNorm_finite_bound (p : FreeGroup ι →₀ ℂ) :
    ∃ (s : Finset ι) (K : ℝ), 0 ≤ K ∧
      ∀ (U V : ι → unitary (groupVonNeumann G)) (δ : ℝ), 0 ≤ δ →
        (∀ j ∈ s, twoNorm ((U j : groupVonNeumann G)-(V j : groupVonNeumann G)) ≤ δ) →
        twoNorm (poly U p-poly V p) ≤ K*δ := by
  classical
  induction p using Finsupp.induction_linear with
  | zero =>
    refine ⟨∅,0,le_rfl,?_⟩
    intro U V δ _hδ _hUV
    simp only [poly_zero,sub_self,twoNorm_zero,zero_mul,le_refl]
  | add p q ihp ihq =>
    obtain ⟨s,K,hK,hb⟩ := ihp
    obtain ⟨t,L,hL,hl⟩ := ihq
    refine ⟨s ∪ t,K+L,add_nonneg hK hL,?_⟩
    intro U V δ hδ hUV
    simp only [poly_add]
    have he : poly U p+poly U q-(poly V p+poly V q) =
        (poly U p-poly V p)+(poly U q-poly V q) := by abel
    rw [he]
    exact (twoNorm_add_le _ _).trans (by
      simpa only [add_mul] using
        add_le_add (hb U V δ hδ (fun j hj => hUV j (Finset.mem_union_left _ hj)))
          (hl U V δ hδ (fun j hj => hUV j (Finset.mem_union_right _ hj))))
  | single g c =>
    obtain ⟨s,K,hK,hb⟩ := word_twoNorm_finite_bound (G := G) g
    refine ⟨s,‖c‖*K,mul_nonneg (norm_nonneg _) hK,?_⟩
    intro U V δ hδ hUV
    simp only [poly_single,← smul_sub,twoNorm_smul]
    exact (mul_le_mul_of_nonneg_left (hb U V δ hδ hUV) (norm_nonneg c)).trans_eq
      (mul_assoc _ _ _).symm

end FreeGroupFactorMain.Generation

namespace FreeGroupFactorMain.InfiniteGeneration
open Generation

 theorem orbit_local_approximation
    (hstep : ∀ (Φ : M ≃⋆ₐ[ℂ] M), (∀ T, canonicalTrace (Φ T) = canonicalTrace T) →
      ∀ (s : Finset Index) (θ : ℝ), 0 < θ →
        ∃ V ∈ orbit, dist V (mapTuple Φ initial) < θ ∧
          ∃ w : Index → FreeGroup (Fin 3), ∀ j ∈ s,
            twoNorm ((wordTuple V w j : M)-(mapTuple Φ generatorUnitary j : M)) < θ)
    (U : Tuple) (hU : U ∈ orbit) (δ : ℝ) (hδ : 0 < δ)
    (g : Group) (ε : ℝ) (hε : 0 < ε) :
    ∃ V ∈ orbit, dist V U < δ ∧ ∃ p : FreeGroup (Fin 3) →₀ ℂ,
      dist (groupL2 (poly V p)) (lp.single 2 g (1 : ℂ)) < ε := by
  classical
  obtain ⟨Φ,ht,rfl⟩ := hU
  obtain ⟨p,hp⟩ := automorphism_poly_dense Φ ht (groupUnitary g) (half_pos hε)
  obtain ⟨s,K,hK,hbound⟩ := poly_twoNorm_finite_bound (G := Group) p
  let θ := min δ (ε/(2*(K+1)))
  have hθ : 0 < θ := lt_min hδ (div_pos hε (by positivity))
  obtain ⟨V,hV,hd,w,hw⟩ := hstep Φ ht s θ hθ
  refine ⟨V,hV,hd.trans_le (min_le_left _ _),substitute w p,?_⟩
  have hb := hbound (wordTuple V w) (mapTuple Φ generatorUnitary) θ hθ.le (fun j hj => (hw j hj).le)
  have hθe : θ*(2*(K+1)) ≤ ε :=
    (le_div_iff₀ (by positivity : 0 < 2*(K+1))).mp (min_le_right _ _)
  have hKe : K*θ < ε/2 := by nlinarith
  rw [dist_eq_norm,← groupL2_groupUnitary g,← map_sub]
  change twoNorm (poly V (substitute w p)-groupUnitary g) < ε
  rw [poly_substitute]
  have he : poly (wordTuple V w) p-groupUnitary g =
      (poly (wordTuple V w) p-poly (mapTuple Φ generatorUnitary) p)+
      (poly (mapTuple Φ generatorUnitary) p-groupUnitary g) := by abel
  rw [he]
  exact (twoNorm_add_le _ _).trans_lt (by linarith)

end FreeGroupFactorMain.InfiniteGeneration

end

end OAI
end

theorem solution : type_of% @OAI.FreeGroupFactorMain.InfiniteGeneration.orbit_local_approximation := @OAI.FreeGroupFactorMain.InfiniteGeneration.orbit_local_approximation
