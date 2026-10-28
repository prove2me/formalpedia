-- Prove2me | solution 1 for OAI.CoveringOrder.optimal_order
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T14:58:19.618951+00:00
-- url     : https://prove2.me/submissions/1f116aa8-b218-44d0-8f14-36d5b3b7de19

import Mathlib
import Definitions.Def_CoveringDensity
import Definitions.Def_OAIQ16Cd002
import Theorems.Thm_OAI_SingleLatticeCovering_Assembly_eventual_single_lattice_covering
import Theorems.Thm_OAI_TranslativeCovering_main
import Theorems.Thm_OAI_TranslativeCovering_periodization_exact

section
-- module Solutions.OAIQ16_CD.LatticeCovering_Products
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open scoped BigOperators
open Real
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Set
noncomputable section
open scoped BigOperators
open MeasureTheory Set
noncomputable section
open Module Submodule MeasureTheory
open scoped BigOperators
noncomputable section
open Real Filter Topology
noncomputable section
open scoped BigOperators
noncomputable section
open Filter Topology Asymptotics
noncomputable section
open scoped BigOperators
open Classical
noncomputable section
open scoped BigOperators
open Classical
noncomputable section
open scoped BigOperators
open Classical
noncomputable section
open scoped BigOperators
noncomputable section
open Module MeasureTheory

namespace SingleLatticeCovering.LatticeGeometry
open Module MeasureTheory
variable {ι : Type*} [Fintype ι] [DecidableEq ι]


lemma mem_image {ι : Type*} [Fintype ι] [DecidableEq ι] (L : Submodule ℤ (ι → ℝ)) (e : (ι → ℝ) ≃ₗ[ℝ] (ι → ℝ)) (x : ι → ℝ) :
    x ∈ image L e ↔ ∃ l ∈ L, e l=x := by
  change e.symm x ∈ L ↔ _
  constructor
  · intro hx; exact ⟨e.symm x,hx,e.apply_symm_apply x⟩
  · rintro ⟨l,hl,rfl⟩; simpa using hl

lemma image_covolume (L : Submodule ℤ (ι → ℝ)) (e : (ι → ℝ) ≃ₗ[ℝ] (ι → ℝ))
    [DiscreteTopology L] [IsZLattice ℝ L] :
    ZLattice.covolume (image L e) = |LinearMap.det e.toLinearMap| * ZLattice.covolume L := by
  let b := IsZLattice.basis L
  let b' : Basis ι ℤ (image L e) := b.ofZLatticeComap ℝ L e.symm
  rw [ZLattice.covolume_eq_det _ b',ZLattice.covolume_eq_det _ b,
    ←Pi.basisFun_det_apply, ←Pi.basisFun_det_apply]
  have he : Subtype.val ∘ b' = e.toLinearMap ∘ (Subtype.val ∘ b) := by
    ext j k
    simp [b', Basis.ofZLatticeComap_apply]
  rw [he, Basis.det_comp, abs_mul]


end SingleLatticeCovering.LatticeGeometry

namespace SingleLatticeCovering.Vertical
open Folded ConstructionA _root_.OAI.SingleLatticeCovering.Blocks LatticeGeometry Module Submodule MeasureTheory
open scoped BigOperators

lemma integerLattice_covolume (n : ℕ) : ZLattice.covolume (integerLattice n) = 1 := by
  rw [ZLattice.covolume_eq_measure_fundamentalDomain _ volume
    (ZSpan.isAddFundamentalDomain (Pi.basisFun ℝ (Fin n)) volume),
    ZSpan.volume_real_fundamentalDomain]
  have hm : Matrix.of (Pi.basisFun ℝ (Fin n)) = (1 : Matrix (Fin n) (Fin n) ℝ) := by
    ext i j
    simp [Pi.basisFun_apply,Pi.single_apply,Matrix.one_apply,eq_comm]
  rw [hm,Matrix.det_one,abs_one]
lemma integer_mem (n : ℕ) (k : Fin n → ℤ) : (fun j => (k j : ℝ)) ∈ integerLattice n := by
  apply ((Pi.basisFun ℝ (Fin n)).mem_span_iff_repr_mem ℤ _).mpr
  intro j
  exact ⟨k j,by simp⟩

end SingleLatticeCovering.Vertical


end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ16_CD.LatticeCovering_Shears
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section



noncomputable section
open MeasureTheory MeasureTheory.Measure Set Module
open scoped Pointwise ENNReal

namespace SingleLatticeCovering.Completion

lemma mem_contractLattice {n : ℕ} (L : Submodule ℤ (RealSpace n))
    (a : ℝ) (ha : a ≠ 0) (x : RealSpace n) :
    x ∈ contractLattice L a ha ↔ a • x ∈ L := Iff.rfl

lemma contractLattice_covolume {n : ℕ} (L : Submodule ℤ (RealSpace n))
    [DiscreteTopology L] [IsZLattice ℝ L] (a : ℝ) (ha : 0 < a) :
    ZLattice.covolume (contractLattice L a ha.ne') = a⁻¹^n * ZLattice.covolume L := by
  let b := IsZLattice.basis L
  let e := LinearEquiv.smulOfNeZero ℝ (RealSpace n) a ha.ne'
  let b' := b.ofZLatticeComap ℝ L e
  let : DiscreteTopology (ZLattice.comap ℝ L e.toLinearMap) := contractLattice_discrete L a ha.ne'
  let : IsZLattice ℝ (ZLattice.comap ℝ L e.toLinearMap) := contractLattice_fullSpan L a ha.ne'
  change ZLattice.covolume (ZLattice.comap ℝ L e.toLinearMap) = _
  rw [ZLattice.covolume_eq_det _ b', ZLattice.covolume_eq_det _ b]
  have hm : Matrix.of (Subtype.val ∘ b') = a⁻¹ • (Matrix.of (Subtype.val ∘ b) : Matrix (Fin n) (Fin n) ℝ) := by
    ext i j
    simp only [Matrix.of_apply, Function.comp_apply, Matrix.smul_apply,
      Basis.ofZLatticeComap_apply, LinearEquiv.smulOfNeZero_symm_apply, Pi.smul_apply,
      smul_eq_mul, b', e]
    simp [Units.smul_def]
  rw [hm, Matrix.det_smul, abs_mul, abs_pow, abs_of_pos (inv_pos.mpr ha), Fintype.card_fin]



end SingleLatticeCovering.Completion

end
end

end

end OAI
end

section
-- module Solutions.OAIQ16_CD.LatticeCovering_Covering
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

namespace SingleLatticeCovering.LatticeGeometry
open MeasureTheory
open scoped Pointwise

lemma affine_image_volume {n : ℕ} (e : (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ))
    (t : Fin n → ℝ) (K : Set (Fin n → ℝ)) :
    volume ((fun x => e x+t) '' K) = ENNReal.ofReal |LinearMap.det e.toLinearMap| * volume K := by
  have hs : (fun x => e x+t) '' K = (fun x => x+t) '' (e '' K) := by
    rw [Set.image_image]
  rw [hs,Set.image_add_right,measure_preimage_add_right]
  exact volume.addHaar_image_linearMap e.toLinearMap K

lemma affine_image_cover {n : ℕ} (L : Submodule ℤ (Fin n → ℝ))
    (e : (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ)) (t : Fin n → ℝ)
    (K : Set (Fin n → ℝ)) (hcover : K+(L : Set (Fin n → ℝ))=Set.univ) :
    (fun x => e x+t) '' K+(image L e : Set (Fin n → ℝ))=Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  have hx : e.symm (x-t) ∈ K+(L : Set (Fin n → ℝ)) := by rw [hcover]; trivial
  obtain ⟨k,hk,l,hl,hkl⟩ := hx
  refine ⟨e k+t,⟨k,hk,rfl⟩,e l,(mem_image L e (e l)).mpr ⟨l,hl,rfl⟩,?_⟩
  change e k+t+e l=x
  have he : e k+e l=x-t := by
    rw [←map_add]
    change k+l=e.symm (x-t) at hkl
    rw [hkl,e.apply_symm_apply]
  calc e k+t+e l = (e k+e l)+t := by abel
       _ = x := by rw [he]; abel

lemma affine_image_density {n : ℕ} (L : Submodule ℤ (Fin n → ℝ))
    [DiscreteTopology L] [IsZLattice ℝ L]
    (e : (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ)) (t : Fin n → ℝ)
    (K : Set (Fin n → ℝ)) :
    (volume ((fun x => e x+t) '' K)).toReal / ZLattice.covolume (image L e) =
      (volume K).toReal / ZLattice.covolume L := by
  rw [affine_image_volume,ENNReal.toReal_mul,ENNReal.toReal_ofReal (abs_nonneg _),image_covolume]
  exact mul_div_mul_left _ _ (abs_ne_zero.mpr e.isUnit_det'.ne_zero)


end SingleLatticeCovering.LatticeGeometry

end

end

end OAI
end

section
-- module Solutions.OAIQ16_CD.LatticeCovering_Horizontal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section

namespace SingleLatticeCovering.Horizontal
open MeasureTheory Completion
open scoped ENNReal BigOperators



attribute [instance] FullLattice.discrete FullLattice.full


end SingleLatticeCovering.Horizontal

end
end

section

noncomputable section
open Set Module MeasureTheory
open scoped BigOperators Pointwise
namespace SingleLatticeCovering.FiniteDimensions




theorem maximal_basis {n : ℕ} (K : Set (Fin n → ℝ)) (hK : IsCompact K)
    (h0 : (0 : Fin n → ℝ) ∈ interior K) :
    ∃ b : Basis (Fin n) ℝ (Fin n → ℝ),
      (∀ j, b j ∈ K) ∧ ∀ x ∈ K, ∀ j, |b.repr x j| ≤ 1 := by
  classical
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp h0)
  let v₀ : Fin n → (Fin n → ℝ) := fun j => (r/2) • Pi.single j (1 : ℝ)
  have hv₀ : ∀ j, v₀ j ∈ K := by
    intro j
    apply hball
    rw [Metric.mem_ball,dist_zero_right]
    simp only [v₀,norm_smul,Pi.norm_single,Real.norm_eq_abs,abs_one,mul_one,
      abs_of_pos (by positivity : 0 < r/2)]
    linarith
  have hdet₀ : (Matrix.of v₀).det = (r/2)^n := by
    have he : Matrix.of v₀ = (r/2) • (1 : Matrix (Fin n) (Fin n) ℝ) := by
      ext i j
      simp [v₀,Pi.single_apply,Matrix.one_apply,Pi.smul_apply,eq_comm]
    rw [he,Matrix.det_smul,Matrix.det_one,mul_one,Fintype.card_fin]
  have hS : IsCompact {v : Fin n → (Fin n → ℝ) | ∀ j, v j ∈ K} :=
    isCompact_pi_infinite (fun _ => hK)
  have hcont : Continuous (fun v : Fin n → (Fin n → ℝ) => |(Matrix.of v).det|) := by
    fun_prop
  obtain ⟨v,hv,hmax⟩ := hS.exists_isMaxOn ⟨v₀,hv₀⟩ hcont.continuousOn
  have hdet : (Matrix.of v).det ≠ 0 := by
    have h : |(Matrix.of v₀).det| ≤ |(Matrix.of v).det| := hmax hv₀
    rw [hdet₀,abs_of_pos (pow_pos (by positivity : 0 < r/2) _)] at h
    intro hz
    rw [hz,abs_zero] at h
    exact (not_le_of_gt (pow_pos (by positivity : 0 < r/2) _)) h
  let b := basisOfLinearIndependentOfCardEqFinrank' v
    (Matrix.linearIndependent_rows_of_det_ne_zero hdet) (by simp)
  have hb : (b : Fin n → (Fin n → ℝ)) = v := by
    simp [b]
  refine ⟨b,?_,?_⟩
  · intro j
    rw [show b j=v j from congrFun hb j]
    exact hv j
  · intro x hx j
    have hupdate : (Function.update v j x) ∈ {v : Fin n → (Fin n → ℝ) | ∀ j, v j ∈ K} := by
      intro k
      by_cases hk : k=j
      · subst k; simpa using hx
      · simpa [hk] using hv k
    have hbound := hmax hupdate
    have hd : (Matrix.of (Function.update v j x)).det = b.repr x j*(Matrix.of v).det := by
      have hs := b.sum_repr x
      have ht := Matrix.det_updateRow_sum (Matrix.of b) j (fun k => b.repr x k)
      change (Matrix.of (Function.update (fun k => b k) j (∑ k, b.repr x k • b k))).det =
        b.repr x j*(Matrix.of b).det at ht
      rw [hs,hb] at ht
      exact ht
    change |(Matrix.of (Function.update v j x)).det| ≤ |(Matrix.of v).det| at hbound
    rw [hd,abs_mul] at hbound
    exact (mul_le_mul_iff_left₀ (abs_pos.mpr hdet)).mp (by simpa [mul_comm] using hbound)


end SingleLatticeCovering.FiniteDimensions

namespace SingleLatticeCovering.FiniteDimensions
open MeasureTheory Module Set Completion Vertical LatticeGeometry
open scoped BigOperators Pointwise

lemma convex_basis_cube {n : ℕ} (hn : 0 < n) (K : Set (Fin n → ℝ))
    (hconv : Convex ℝ K) (h0 : (0 : Fin n → ℝ) ∈ K)
    (b : Basis (Fin n) ℝ (Fin n → ℝ)) (hb : ∀ j, b j ∈ K) :
    Icc (0 : Fin n → ℝ) (fun _ => 1/(n : ℝ)) ⊆ b.equivFun.symm ⁻¹' K := by
  intro x hx
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have hsum : ∑ j, x j ≤ 1 := calc
    ∑ j, x j ≤ ∑ _j : Fin n, 1/(n : ℝ) := Finset.sum_le_sum (fun j _ => hx.2 j)
    _ = 1 := by simp [hnr.ne']
  let w : Fin (n+1) → ℝ := Fin.cons (1-∑ j, x j) x
  let z : Fin (n+1) → (Fin n → ℝ) := Fin.cons 0 b
  have hw : ∀ j ∈ (Finset.univ : Finset (Fin (n+1))), 0 ≤ w j := by
    intro j _
    refine Fin.cases ?_ (fun i => ?_) j
    · exact sub_nonneg.mpr hsum
    · exact hx.1 i
  have hw1 : ∑ j, w j = 1 := by simp [w,Fin.sum_univ_succ]
  have hz : ∀ j ∈ (Finset.univ : Finset (Fin (n+1))), z j ∈ K := by
    intro j _
    exact Fin.cases h0 hb j
  have hc := hconv.sum_mem hw hw1 hz
  change b.equivFun.symm x ∈ K
  rw [Basis.equivFun_symm_apply]
  simpa only [Fin.sum_univ_succ,w,z,Fin.cons_zero,Fin.cons_succ,smul_zero,zero_add] using hc

lemma integer_cube_cover {n : ℕ} (hn : 0 < n) :
    Icc (0 : Fin n → ℝ) (fun _ => 1/(n : ℝ))+
      (contractLattice (integerLattice n) (n : ℝ) (by exact_mod_cast hn.ne') : Set (Fin n → ℝ)) =
      Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  let l : Fin n → ℝ := fun j => (⌊(n : ℝ)*x j⌋ : ℤ)/(n : ℝ)
  let q : Fin n → ℝ := fun j => Int.fract ((n : ℝ)*x j)/(n : ℝ)
  have hl : l ∈ contractLattice (integerLattice n) (n : ℝ) (by exact_mod_cast hn.ne') := by
    rw [mem_contractLattice]
    convert integer_mem n (fun j => ⌊(n : ℝ)*x j⌋) using 1
    all_goals try with_reducible_and_instances rfl
    ext j
    simp only [Pi.smul_apply,smul_eq_mul,l]
    field_simp
  refine ⟨q,⟨?_,?_⟩,l,hl,?_⟩
  · intro j
    exact div_nonneg (Int.fract_nonneg _) hnr.le
  · intro j
    exact (div_le_div_iff_of_pos_right hnr).mpr (Int.fract_lt_one _).le
  · ext j
    change Int.fract ((n : ℝ)*x j)/(n : ℝ)+(⌊(n : ℝ)*x j⌋ : ℤ)/(n : ℝ)=x j
    rw [←add_div,Int.fract_add_floor]
    exact mul_div_cancel_left₀ _ hnr.ne'



end SingleLatticeCovering.FiniteDimensions

namespace SingleLatticeCovering.FiniteDimensions
open MeasureTheory Module Set Completion Vertical LatticeGeometry
open scoped BigOperators Pointwise



theorem finite_dimension_cover {n : ℕ} (hn : 0 < n)
    (K : Set (Fin n → ℝ)) (hK : IsCompact K) (hconv : Convex ℝ K)
    (hinterior : (interior K).Nonempty) :
    ∃ (L : Submodule ℤ (Fin n → ℝ)) (_ : DiscreteTopology L),
      IsZLattice ℝ L ∧ K+(L : Set (Fin n → ℝ))=univ ∧
      (volume K).toReal / ZLattice.covolume L ≤ (2*(n : ℝ))^n := by
  classical
  obtain ⟨x₀,hx₀⟩ := hinterior
  let t := Homeomorph.addRight x₀
  let K₀ := t ⁻¹' K
  have hK₀ : IsCompact K₀ := t.isCompact_preimage.mpr hK
  have h0 : (0 : Fin n → ℝ) ∈ interior K₀ := by
    rw [←t.preimage_interior]
    change 0+x₀ ∈ interior K
    simpa using hx₀
  have hconv₀ : Convex ℝ K₀ := by
    intro x hx y hy a b ha hb hab
    have hh := hconv hx hy ha hb hab
    change a • (x+x₀)+b • (y+x₀) ∈ K at hh
    change a • x+b • y+x₀ ∈ K
    have he : a • (x+x₀)+b • (y+x₀) = a • x+b • y+x₀ := by
      calc
        _ = (a • x+b • y)+(a+b) • x₀ := by module
        _ = _ := by rw [hab,one_smul]
    rwa [he] at hh
  obtain ⟨b,hb,hbound⟩ := maximal_basis K₀ hK₀ h0
  let e := b.equivFun.symm
  let K' := e ⁻¹' K₀
  have hsmall : Icc (0 : Fin n → ℝ) (fun _ => 1/(n : ℝ)) ⊆ K' :=
    convex_basis_cube hn K₀ hconv₀ (interior_subset h0) b hb
  have hlarge : K' ⊆ Icc (fun _ : Fin n => (-1 : ℝ)) (fun _ => 1) := by
    intro x hx
    have hb' := hbound (e x) hx
    have hj (j : Fin n) : |x j| ≤ 1 := by
      have hh : |b.equivFun (e x) j| ≤ 1 := hb' j
      simpa only [e,LinearEquiv.apply_symm_apply] using hh
    exact ⟨fun j => (abs_le.mp (hj j)).1,fun j => (abs_le.mp (hj j)).2⟩
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  let L₀ := contractLattice (integerLattice n) (n : ℝ) hnr.ne'
  have hcover : K'+(L₀ : Set (Fin n → ℝ))=univ := by
    apply Set.eq_univ_of_univ_subset
    rw [←integer_cube_cover hn]
    exact Set.add_subset_add_right hsmall
  have hvolume : (volume K').toReal ≤ (2 : ℝ)^n := by
    have hh := ENNReal.toReal_mono (isCompact_Icc.measure_ne_top (μ := volume)) (measure_mono hlarge)
    rw [Real.volume_Icc_pi_toReal (by intro j; norm_num)] at hh
    norm_num at hh
    exact hh
  have hcov : ZLattice.covolume L₀ = (n : ℝ)⁻¹^n := by
    rw [contractLattice_covolume _ _ hnr,integerLattice_covolume,mul_one]
  have hdens : (volume K').toReal / ZLattice.covolume L₀ ≤ (2*(n : ℝ))^n := by
    rw [hcov,inv_pow,div_inv_eq_mul,mul_pow]
    exact mul_le_mul_of_nonneg_right hvolume (pow_nonneg hnr.le _)
  have himage : (fun x => e x+x₀) '' K'=K := by
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      exact hy
    · intro hx
      refine ⟨e.symm (x-x₀),?_,?_⟩
      · change e (e.symm (x-x₀))+x₀ ∈ K
        simpa using hx
      · simp
  refine ⟨image L₀ e,inferInstance,inferInstance,?_,?_⟩
  · rw [←himage]
    exact affine_image_cover L₀ e x₀ K' hcover
  · rw [←himage,affine_image_density]
    exact hdens


end SingleLatticeCovering.FiniteDimensions


end
end
end

end OAI
end

section
-- module Solutions.OAIQ16_CD.LatticeCovering_Isotropy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Module MeasureTheory
open scoped BigOperators Pointwise

namespace SingleLatticeCovering.FiniteDimensions
open Filter MeasureTheory
open scoped Pointwise BigOperators




lemma absorb_finitely_many_dimensions
    (h : ∃ C : ℝ, ∀ᶠ n : ℕ in atTop, ∀ K : Set (Fin n → ℝ),
      IsCompact K → Convex ℝ K → (interior K).Nonempty →
      ∃ (L : Submodule ℤ (Fin n → ℝ)) (_ : DiscreteTopology L),
        IsZLattice ℝ L ∧ K+(L : Set (Fin n → ℝ))=Set.univ ∧
        (volume K).toReal / ZLattice.covolume L ≤ C*(n : ℝ)*Real.log (n : ℝ)) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 2 ≤ n → ∀ K : Set (Fin n → ℝ),
      IsCompact K → Convex ℝ K → (interior K).Nonempty →
      ∃ (L : Submodule ℤ (Fin n → ℝ)) (_ : DiscreteTopology L),
        IsZLattice ℝ L ∧ K+(L : Set (Fin n → ℝ))=Set.univ ∧
        (volume K).toReal / ZLattice.covolume L ≤ C*(n : ℝ)*Real.log (n : ℝ) := by
  classical
  obtain ⟨C,hC⟩ := h
  obtain ⟨N,hN⟩ := eventually_atTop.mp hC
  let f : ℕ → ℝ := fun n => (2*(n : ℝ))^n / ((n : ℝ)*Real.log (n : ℝ))
  have hf : ∀ n, 0 ≤ f n := fun n => div_nonneg (by positivity)
    (mul_nonneg (Nat.cast_nonneg _) (Real.log_natCast_nonneg _))
  let S := ∑ n ∈ Finset.range N, f n
  have hS : 0 ≤ S := Finset.sum_nonneg (fun n _ => hf n)
  refine ⟨1+|C|+S,by positivity,?_⟩
  intro n hn K hK hc hi
  have hnr : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hlog : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  by_cases hlarge : N ≤ n
  · obtain ⟨L,hd,hfull,hcover,hbound⟩ := hN n hlarge K hK hc hi
    refine ⟨L,hd,hfull,hcover,hbound.trans ?_⟩
    gcongr
    exact le_trans (le_abs_self C) (by linarith)
  · obtain ⟨L,hd,hfull,hcover,hbound⟩ := finite_dimension_cover (by omega) K hK hc hi
    refine ⟨L,hd,hfull,hcover,hbound.trans ?_⟩
    have hnN : n ∈ Finset.range N := Finset.mem_range.mpr (by omega)
    have hfS : f n ≤ S := Finset.single_le_sum (fun i _ => hf i) hnN
    have hff : f n ≤ 1+|C|+S := hfS.trans (by linarith [abs_nonneg C])
    rw [mul_assoc]
    exact (div_le_iff₀ (mul_pos hnr hlog)).mp hff


end SingleLatticeCovering.FiniteDimensions

end
end

end

end OAI
end

section
-- module Solutions.OAIQ16_CD.LatticeCovering_Main
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A uniform, unconditional single-lattice covering bound in every dimension at least two.
The eventual bound uses the proved analytic and geometric producers; finite-dimensional
absorption supplies one absolute constant for all dimensions. -/

noncomputable section

namespace SingleLatticeCovering
open MeasureTheory
open scoped Pointwise











theorem single_lattice_covering :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ), 2 ≤ n →
      ∀ (K : Set (Space n)), IsConvexBody K →
        ∃ (L : Submodule ℤ (Space n)) (_ : DiscreteTopology L),
          IsZLattice ℝ L ∧ LatticeCovers K L ∧
            (volume K).toReal / ZLattice.covolume L ≤ C * (n : ℝ) * Real.log (n : ℝ) := by
  obtain ⟨C,hC,h⟩ := Assembly.eventual_single_lattice_covering
  obtain ⟨C',hC',h'⟩ := FiniteDimensions.absorb_finitely_many_dimensions ⟨C,h⟩
  exact ⟨C',hC',fun n hn K hK => h' n hn K hK.1 hK.2.1 hK.2.2⟩


end SingleLatticeCovering



end

end OAI
end

section
-- module Solutions.OAIQ16_CD.CoveringDensity_EuclideanTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The coordinate map is a continuous linear equivalence and preserves volume.
The Euclidean norm and the coordinate supremum norm need not agree. -/
noncomputable section
open Set MeasureTheory
open scoped Pointwise ENNReal
namespace CoveringOrder

theorem euclidean_lattice_upper :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 2 ≤ n →
      ∀ K : Set (EuclideanSpace ℝ (Fin n)), TranslativeCovering.ConvexBody K →
        ∃ (L : Submodule ℤ (EuclideanSpace ℝ (Fin n))) (_ : DiscreteTopology L),
          IsZLattice ℝ L ∧ (∀ y, ∃ l : L, y - l.val ∈ K) ∧
            volume K / ENNReal.ofReal (ZLattice.covolume L volume) ≤
              ENNReal.ofReal (C * (n : ℝ) * Real.log n) := by
  obtain ⟨C, hC, hupper⟩ := SingleLatticeCovering.single_lattice_covering
  refine ⟨C, hC, ?_⟩
  intro n hn K hK
  let e : EuclideanSpace ℝ (Fin n) ≃L[ℝ] (Fin n → ℝ) :=
    (WithLp.linearEquiv 2 ℝ (Fin n → ℝ)).toContinuousLinearEquiv
  have hp : MeasurePreserving e volume volume := PiLp.volume_preserving_ofLp (Fin n)
  have hc : IsCompact (e '' K) := hK.1.image e.continuous
  have hbody : SingleLatticeCovering.IsConvexBody (e '' K) := by
    refine ⟨hc, hK.2.1.linear_image e.toLinearMap, ?_⟩
    change (interior (e.toHomeomorph '' K)).Nonempty
    rw [← e.toHomeomorph.image_interior]
    exact hK.2.2.image e
  have hvol : volume (e '' K) = volume K := by
    have hm := hp.measure_preimage hc.measurableSet.nullMeasurableSet
    rw [Set.preimage_image_eq _ e.injective] at hm
    exact hm.symm
  obtain ⟨L, hd, hf, hcover, hbound⟩ := hupper n hn (e '' K) hbody
  let : DiscreteTopology L := hd
  let : IsZLattice ℝ L := hf
  let Λ := ZLattice.comap ℝ L e.toLinearMap
  have hcov : ZLattice.covolume Λ volume = ZLattice.covolume L volume :=
    ZLattice.covolume_comap L volume volume hp
  refine ⟨Λ, inferInstance, inferInstance, ?_, ?_⟩
  · intro y
    have hy : e y ∈ e '' K + (L : Set (Fin n → ℝ)) := by
      rw [hcover]
      trivial
    obtain ⟨k, ⟨x, hx, rfl⟩, l, hl, heq⟩ := hy
    have hl' : e.symm l ∈ Λ := by
      change e (e.symm l) ∈ L
      rw [e.apply_symm_apply]
      exact hl
    refine ⟨⟨e.symm l, hl'⟩, ?_⟩
    have hxy : x + e.symm l = y := by
      apply e.injective
      simpa only [map_add, e.apply_symm_apply] using heq
    have hdiff : y - e.symm l = x := by rw [← hxy]; abel
    simpa only [hdiff] using hx
  · rw [hvol] at hbound
    have hpos : 0 < ZLattice.covolume L volume := ZLattice.covolume_pos L volume
    rw [hcov]
    calc
      volume K / ENNReal.ofReal (ZLattice.covolume L volume) =
          ENNReal.ofReal ((volume K).toReal / ZLattice.covolume L volume) := by
            rw [ENNReal.ofReal_div_of_pos hpos, ENNReal.ofReal_toReal hK.1.measure_ne_top]
      _ ≤ ENNReal.ofReal (C * (n : ℝ) * Real.log n) := ENNReal.ofReal_le_ofReal hbound

end CoveringOrder

end

end OAI
end

section
-- module Solutions.OAIQ16_CD.TranslativeCovering_DistinctCosets
attribute [-instance] _root_.OAI.SingleLatticeCovering.LatticeGeometry.prod_discrete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open MeasureTheory ProbabilityTheory Set
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open Set MeasureTheory
open scoped ENNReal Classical
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open MeasureTheory ProbabilityTheory Set
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open Set MeasureTheory
open scoped ENNReal Classical
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal

namespace TranslativeCovering
open Set MeasureTheory
open scoped ENNReal Classical

lemma PeriodicCover.remove_repeats {n : ℕ} {K : Set (Space n)} (P : PeriodicCover K) :
    ∃ Q : PeriodicCover K,Q.Distinct ∧ Q.intensity≤P.intensity := by
  let S : Finset (Space n ⧸ P.lattice) := Finset.univ.image P.coset
  have hex (s : S) : ∃ i : Fin P.m,P.coset i=s.val := by
    obtain ⟨i,_,hi⟩ := Finset.mem_image.mp s.property
    exact ⟨i,hi⟩
  let r : S → Fin P.m := fun s => Classical.choose (hex s)
  have hr (s : S) : P.coset (r s)=s.val := Classical.choose_spec (hex s)
  let e := Finset.equivFin S
  let Q : PeriodicCover K := {
    lattice := P.lattice
    discrete := P.discrete
    fullrank := P.fullrank
    m := S.card
    offsets := fun j => P.offsets (r (e.symm j))
    covers := by
      intro y
      obtain ⟨i,l,hy⟩ := P.covers y
      let s : S := ⟨P.coset i,Finset.mem_image.mpr ⟨i,Finset.mem_univ i,rfl⟩⟩
      have heq : P.coset i=P.coset (r s) := (hr s).symm
      have hmem : P.offsets i-P.offsets (r s) ∈ P.lattice := (Submodule.Quotient.eq P.lattice).mp heq
      refine ⟨e s,⟨P.offsets i-P.offsets (r s)+l.val,P.lattice.add_mem hmem l.property⟩,?_⟩
      simp only [Equiv.symm_apply_apply]
      have he : y - P.offsets (r s) - (P.offsets i - P.offsets (r s) + l.val) =
          y - P.offsets i - l.val := by abel
      simpa only [he] using hy }
  refine ⟨Q,?_,?_⟩
  · intro j k hjk
    change P.coset (r (e.symm j))=P.coset (r (e.symm k)) at hjk
    rw [hr,hr] at hjk
    exact e.symm.injective (Subtype.ext hjk)
  · change (S.card:ℝ≥0∞)/ENNReal.ofReal (ZLattice.covolume P.lattice volume)≤
      (P.m:ℝ≥0∞)/ENNReal.ofReal (ZLattice.covolume P.lattice volume)
    apply ENNReal.div_le_div_right
    have hc : S.card≤P.m := by simpa only [S,Finset.card_univ,Fintype.card_fin] using (Finset.card_image_le (s:=Finset.univ) (f:=P.coset))
    exact_mod_cast hc

lemma listed_eq_distinct {n : ℕ} (K : Set (Space n)) : thetaPerListed K=thetaPer K := by
  apply le_antisymm
  · apply le_iInf
    intro P
    exact iInf_le (fun Q : PeriodicCover K => volume K*Q.intensity) P.val
  · apply le_iInf
    intro P
    obtain ⟨Q,hQ,hQP⟩ := P.remove_repeats
    exact (iInf_le (fun Q : {P : PeriodicCover K // P.Distinct} => volume K*Q.val.intensity) ⟨Q,hQ⟩).trans
      (mul_le_mul le_rfl hQP bot_le bot_le)

end TranslativeCovering

end OAI
end

section
-- module Solutions.OAIQ16_CD.CoveringDensity_Main
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CoveringOrder
open Set MeasureTheory
open scoped ENNReal

theorem euclideanVolume_eq_volume (n : ℕ) : euclideanVolume n = volume :=
  (PiLp.volume_preserving_toLp (Fin n)).map_eq

theorem euclideanCovolume_eq_ofReal {n : ℕ} (lattice : Submodule ℤ (Space n))
    [DiscreteTopology lattice] [IsZLattice ℝ lattice] :
    euclideanCovolume lattice = ENNReal.ofReal (ZLattice.covolume lattice volume) := by
  rw [euclideanCovolume, euclideanVolume_eq_volume, ZLattice.covolume]
  apply (ENNReal.ofReal_toReal ?_).symm
  intro htop
  apply ZLattice.covolume_ne_zero lattice volume
  simp only [ZLattice.covolume, htop, ENNReal.toReal_top]

theorem latticeDensity_eq_volume_div_covolume {n : ℕ} {K : Set (Space n)}
    (cover : LatticeCover K) :
    latticeDensity cover = volume K / ENNReal.ofReal (ZLattice.covolume cover.lattice volume) := by
  let := cover.discrete
  let := cover.fullrank
  simp only [latticeDensity, euclideanVolume_eq_volume, euclideanCovolume_eq_ofReal]

/-- The infimum of actual lattice densities agrees with indexing by bundled covers. -/
theorem thetaL_eq_iInf_latticeCover {n : ℕ} (K : Set (Space n)) :
    thetaL K = ⨅ P : LatticeCover K,
      volume K / ENNReal.ofReal (ZLattice.covolume P.lattice volume) := by
  unfold thetaL
  exact iInf_congr latticeDensity_eq_volume_div_covolume

/-- Full periodization, followed by restriction to one-coset coverings. -/
theorem thetaT_le_thetaL {n : ℕ} {K : Set (Space n)}
    (hK : TranslativeCovering.ConvexBody K) :
    TranslativeCovering.thetaT K ≤ thetaL K := by
  rw [thetaL_eq_iInf_latticeCover, TranslativeCovering.periodization_exact hK,
    ← TranslativeCovering.listed_eq_distinct K]
  apply le_iInf
  intro P
  have h := iInf_le
    (fun Q : TranslativeCovering.PeriodicCover K => volume K * Q.intensity)
    P.toPeriodic
  simpa only [TranslativeCovering.thetaPerListed,
    TranslativeCovering.PeriodicCover.intensity, LatticeCover.toPeriodic,
    Nat.cast_one, one_div, div_eq_mul_inv, one_mul] using h

/-- The transported upper theorem bounds the actual lattice-density infimum. -/
theorem uniform_lattice_density_upper :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 2 ≤ n → ∀ K : Set (Space n),
      TranslativeCovering.ConvexBody K →
      thetaL K ≤ ENNReal.ofReal (C * (n : ℝ) * Real.log (n : ℝ)) := by
  obtain ⟨C, hC, h⟩ := euclidean_lattice_upper
  refine ⟨C, hC, ?_⟩
  intro n hn K hK
  obtain ⟨L, hd, hf, hc, hb⟩ := h n hn K hK
  let P : LatticeCover K := ⟨L, hd, hf, hc⟩
  rw [thetaL_eq_iInf_latticeCover]
  exact (iInf_le (fun Q : LatticeCover K =>
    volume K / ENNReal.ofReal (ZLattice.covolume Q.lattice volume)) P).trans hb

/-- All four density suprema have order `n * log n` with common absolute constants. -/
theorem optimal_order_oai : OptimalOrder := by
  obtain ⟨c, hc, n₀, hlower⟩ := TranslativeCovering.main
  obtain ⟨C, hC, hupper⟩ := uniform_lattice_density_upper
  refine ⟨c, C, hc, hC, max n₀ 2, ?_⟩
  intro n hn
  have hn₀ : n₀ ≤ n := (le_max_left _ _).trans hn
  have hn₂ : 2 ≤ n := (le_max_right _ _).trans hn
  obtain ⟨K, hK, hsym, hlow⟩ := hlower n hn₀
  let B : Body n := ⟨K, hK⟩
  let S : SymmetricBody n := ⟨B, hsym⟩
  have t_upper (A : Body n) :
      TranslativeCovering.thetaT A.val ≤
        ENNReal.ofReal (C * (n : ℝ) * Real.log (n : ℝ)) :=
    (thetaT_le_thetaL A.property).trans (hupper n hn₂ A.val A.property)
  have l_upper (A : Body n) :
      thetaL A.val ≤ ENNReal.ofReal (C * (n : ℝ) * Real.log (n : ℝ)) :=
    hupper n hn₂ A.val A.property
  have tl : ENNReal.ofReal (c * (n : ℝ) * Real.log (n : ℝ)) ≤
      TranslativeCovering.thetaT K := hlow.le
  have ll : ENNReal.ofReal (c * (n : ℝ) * Real.log (n : ℝ)) ≤ thetaL K :=
    tl.trans (thetaT_le_thetaL hK)
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · exact tl.trans (le_iSup (fun A : Body n => TranslativeCovering.thetaT A.val) B)
  · exact iSup_le t_upper
  · exact tl.trans (le_iSup
      (fun A : SymmetricBody n => TranslativeCovering.thetaT A.val.val) S)
  · exact iSup_le (fun A : SymmetricBody n => t_upper A.val)
  · exact ll.trans (le_iSup (fun A : Body n => thetaL A.val) B)
  · exact iSup_le l_upper
  · exact ll.trans (le_iSup (fun A : SymmetricBody n => thetaL A.val.val) S)
  · exact iSup_le (fun A : SymmetricBody n => l_upper A.val)

end CoveringOrder

end OAI
end

theorem solution : type_of% @OAI.CoveringOrder.optimal_order_oai := @OAI.CoveringOrder.optimal_order_oai
