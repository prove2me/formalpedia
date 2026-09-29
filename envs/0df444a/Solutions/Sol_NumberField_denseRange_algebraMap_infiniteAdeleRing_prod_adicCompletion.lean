-- Prove2me | solution 1 for NumberField.denseRange_algebraMap_infiniteAdeleRing_prod_adicCompletion
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/c2cc9a38-202a-5eb1-a743-e721bcf30094

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_denseRange_algebraMap_infiniteAdeleRing_prod_adicCompletion

set_option autoImplicit false

p2m_open "NumberField P2MW.S_NumberField_denseRange_algebraMap_infiniteAdeleRing_prod_adicCompletion.NumberField IsDedekindDomain Filter"
open scoped Topology

namespace NumberField
p2m_export "NumberField" "FinitePlace FinitePlace.norm_lt_one_iff_mem InfiniteAdeleRing place FinitePlace.norm_eq_one_iff_notMem InfinitePlace.denseRange_algebraMap_pi FinitePlace.norm_embedding HeightOneSpectrum.adicAbv InfinitePlace.eq_iff_isEquiv HeightOneSpectrum.adicAbv_natCast_le_one InfinitePlace InfinitePlace.coe_apply"
namespace WeakApprox
p2m_open "NumberField"

variable (K : Type*) [Field K] [NumberField K]

noncomputable def absFamily (S : Finset (HeightOneSpectrum (𝓞 K))) :
    InfinitePlace K ⊕ ↥S → AbsoluteValue K ℝ :=
  Sum.elim (fun w => w.1) (fun v => NumberField.HeightOneSpectrum.adicAbv K v.1)

theorem absFamily_inl (S : Finset (HeightOneSpectrum (𝓞 K))) (w : InfinitePlace K) :
    absFamily K S (Sum.inl w) = w.1 := rfl

theorem absFamily_inr (S : Finset (HeightOneSpectrum (𝓞 K))) (v : ↥S) :
    absFamily K S (Sum.inr v) = NumberField.HeightOneSpectrum.adicAbv K v.1 := rfl

theorem adicAbv_isNontrivial (v : HeightOneSpectrum (𝓞 K)) : (NumberField.HeightOneSpectrum.adicAbv K v).IsNontrivial := by
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot v.ne_bot
  refine ⟨algebraMap (𝓞 K) K x, by simpa using hx0, ?_⟩
  have : NumberField.HeightOneSpectrum.adicAbv K v (algebraMap (𝓞 K) K x) < 1 := by
    rw [← FinitePlace.norm_embedding]
    exact (FinitePlace.norm_lt_one_iff_mem K v x).2 hx
  exact this.ne

theorem adicAbv_not_isEquiv_of_ne {v v' : HeightOneSpectrum (𝓞 K)} (h : v ≠ v') :
    ¬ (NumberField.HeightOneSpectrum.adicAbv K v).IsEquiv (NumberField.HeightOneSpectrum.adicAbv K v') := by
  intro heq

  have hne : ¬ v.asIdeal ≤ v'.asIdeal := by
    intro hle
    exact h (HeightOneSpectrum.ext (v.isMaximal.eq_of_le v'.isPrime.ne_top hle))
  obtain ⟨x, hxv, hxv'⟩ := SetLike.not_le_iff_exists.1 hne
  have h1 : NumberField.HeightOneSpectrum.adicAbv K v (algebraMap (𝓞 K) K x) < 1 := by
    rw [← FinitePlace.norm_embedding]
    exact (FinitePlace.norm_lt_one_iff_mem K v x).2 hxv
  have h2 : NumberField.HeightOneSpectrum.adicAbv K v' (algebraMap (𝓞 K) K x) = 1 := by
    rw [← FinitePlace.norm_embedding]
    exact (FinitePlace.norm_eq_one_iff_notMem K v' x).2 hxv'
  have := (AbsoluteValue.isEquiv_iff_lt_one_iff.1 heq (algebraMap (𝓞 K) K x)).1 h1
  rw [h2] at this
  exact lt_irrefl _ this

theorem infinitePlace_adicAbv_not_isEquiv (w : InfinitePlace K) (v : HeightOneSpectrum (𝓞 K)) :
    ¬ w.1.IsEquiv (NumberField.HeightOneSpectrum.adicAbv K v) := by
  intro heq
  have h2 : (2 : K) ≠ 0 := two_ne_zero
  have hw : w.1 (2 : K)⁻¹ < 1 := by
    rw [map_inv₀]
    have : w.1 (2 : K) = 2 := by
      have := w.map_natCast 2
      simpa [InfinitePlace.coe_apply] using this
    rw [this]
    norm_num
  have hv : ¬ NumberField.HeightOneSpectrum.adicAbv K v (2 : K)⁻¹ < 1 := by
    rw [map_inv₀, not_lt]
    have hle : NumberField.HeightOneSpectrum.adicAbv K v (2 : K) ≤ 1 := by exact_mod_cast NumberField.HeightOneSpectrum.adicAbv_natCast_le_one K v 2
    have hpos : 0 < NumberField.HeightOneSpectrum.adicAbv K v (2 : K) := (NumberField.HeightOneSpectrum.adicAbv K v).pos h2
    exact one_le_inv_iff₀.2 ⟨hpos, hle⟩
  exact hv ((AbsoluteValue.isEquiv_iff_lt_one_iff.1 heq _).1 hw)

theorem absFamily_isNontrivial (S : Finset (HeightOneSpectrum (𝓞 K))) (i : InfinitePlace K ⊕ ↥S) :
    (absFamily K S i).IsNontrivial := by
  cases i with
  | inl w => exact w.isNontrivial
  | inr v => exact adicAbv_isNontrivial K v.1

theorem absFamily_pairwise_not_isEquiv (S : Finset (HeightOneSpectrum (𝓞 K))) :
    Pairwise fun i j => ¬ (absFamily K S i).IsEquiv (absFamily K S j) := by
  intro i j hij
  cases i with
  | inl w =>
    cases j with
    | inl w' =>
      rw [absFamily_inl, absFamily_inl]
      exact (InfinitePlace.eq_iff_isEquiv (K := K)).not.mp fun h => hij (by rw [h])
    | inr v => exact infinitePlace_adicAbv_not_isEquiv K w v.1
  | inr v =>
    cases j with
    | inl w => exact fun h => infinitePlace_adicAbv_not_isEquiv K w v.1 h.symm
    | inr v' =>
      rw [absFamily_inr, absFamily_inr]
      exact adicAbv_not_isEquiv_of_ne K fun h => hij (by rw [Subtype.ext h])

theorem denseRange_algebraMap_pi_withAbs (S : Finset (HeightOneSpectrum (𝓞 K))) :
    DenseRange <| algebraMap K ((i : InfinitePlace K ⊕ ↥S) → WithAbs (absFamily K S i)) := by
  classical
  refine Metric.denseRange_iff.mpr fun z r hr ↦ ?_
  choose a hx using AbsoluteValue.exists_one_lt_lt_one_pi_of_not_isEquiv (absFamily_isNontrivial K S)
    (absFamily_pairwise_not_isEquiv K S)
  let y := fun n ↦ ∑ i, (1 / (1 + (a i)⁻¹ ^ n)) * WithAbs.equiv (absFamily K S i) (z i)
  have : atTop.Tendsto
      (fun n (i : InfinitePlace K ⊕ ↥S) ↦ (WithAbs.equiv (absFamily K S i)).symm (y n)) (𝓝 z) := by
    refine tendsto_pi_nhds.mpr fun u ↦ ?_
    simp_rw [← Fintype.sum_pi_single u z, y, map_sum, map_mul]
    refine tendsto_finsetSum _ fun w _ ↦ ?_
    by_cases hw : u = w
    · rw [← hw, Pi.single_eq_same]
      have : absFamily K S u (a u)⁻¹ < 1 := by
        simpa [← inv_pow, inv_lt_one_iff₀] using .inr (hx u).1
      simpa using (WithAbs.tendsto_one_div_one_add_pow_nhds_one this).mul_const (z u)
    · rw [Pi.single_eq_of_ne (M := fun i ↦ WithAbs (absFamily K S i)) hw (z w)]
      have hpos : 0 < absFamily K S u (a w) := by
        refine (absFamily K S u).pos fun ha => ?_
        have h1 := (hx w).1
        rw [ha, map_zero] at h1
        linarith
      have ha0 : a w ≠ 0 := fun ha => by
        have h1 := (hx w).1
        rw [ha, map_zero] at h1
        linarith
      have hu : 1 < absFamily K S u (a w)⁻¹ := by
        rw [map_inv₀, one_lt_inv_iff₀]
        exact ⟨hpos, (hx w).2 u hw⟩
      have := (absFamily K S u).tendsto_div_one_add_pow_nhds_zero hu
      simp_rw [← WithAbs.norm_toAbs_eq] at this
      simpa using (tendsto_zero_iff_norm_tendsto_zero.2 this).mul_const
        ((WithAbs.equiv (absFamily K S u)).symm (WithAbs.equiv (absFamily K S w) (z w)))
  let ⟨N, h⟩ := Metric.tendsto_atTop.1 this r hr
  exact ⟨y N, dist_comm z (algebraMap K _ (y N)) ▸ h N le_rfl⟩

abbrev MixedSpace (S : Finset (HeightOneSpectrum (𝓞 K))) : Type _ :=
  InfiniteAdeleRing K × ((v : ↥S) → v.1.adicCompletion K)

noncomputable def mixedEmb (S : Finset (HeightOneSpectrum (𝓞 K))) (x : K) : MixedSpace K S :=
  (algebraMap K (InfiniteAdeleRing K) x, fun v => algebraMap K (v.1.adicCompletion K) x)

noncomputable def toMixed (S : Finset (HeightOneSpectrum (𝓞 K)))
    (y : (i : InfinitePlace K ⊕ ↥S) → WithAbs (absFamily K S i)) : MixedSpace K S :=
  (fun w => ((show WithAbs w.1 from y (Sum.inl w)) : w.Completion),
    fun v => algebraMap K (v.1.adicCompletion K) (WithAbs.equiv (NumberField.HeightOneSpectrum.adicAbv K v.1) (y (Sum.inr v))))

theorem continuous_adicCompletion_of_withAbs (v : HeightOneSpectrum (𝓞 K)) :
    Continuous fun y : WithAbs (NumberField.HeightOneSpectrum.adicAbv K v) => algebraMap K (v.adicCompletion K) (WithAbs.equiv (NumberField.HeightOneSpectrum.adicAbv K v) y) := by

  let f : WithAbs (NumberField.HeightOneSpectrum.adicAbv K v) →+ v.adicCompletion K :=
    { toFun := fun y => algebraMap K (v.adicCompletion K) (WithAbs.equiv (NumberField.HeightOneSpectrum.adicAbv K v) y)
      map_zero' := by simp
      map_add' := fun a b => by simp }
  have hf : ∀ y, ‖f y‖ = ‖y‖ := by
    intro y
    show ‖algebraMap K (v.adicCompletion K) (WithAbs.equiv (NumberField.HeightOneSpectrum.adicAbv K v) y)‖ = ‖y‖
    rw [WithAbs.norm_eq_apply_ofAbs, ← FinitePlace.norm_embedding]
    rfl
  exact (AddMonoidHomClass.isometry_of_norm f hf).continuous

theorem continuous_toMixed (S : Finset (HeightOneSpectrum (𝓞 K))) : Continuous (toMixed K S) := by
  refine Continuous.prodMk ?_ ?_
  · exact continuous_pi fun w => (NumberField.InfinitePlace.Completion.continuous_coe _).comp (continuous_apply _)
  · exact continuous_pi fun v => (continuous_adicCompletion_of_withAbs K v.1).comp (continuous_apply _)

theorem denseRange_toMixed (S : Finset (HeightOneSpectrum (𝓞 K))) : DenseRange (toMixed K S) := by

  let e : ((i : InfinitePlace K ⊕ ↥S) → WithAbs (absFamily K S i)) ≃
      ((w : InfinitePlace K) → WithAbs w.1) × ((v : ↥S) → WithAbs (NumberField.HeightOneSpectrum.adicAbv K v.1)) :=
    { toFun := fun y => (fun w => y (Sum.inl w), fun v => y (Sum.inr v))
      invFun := fun p => fun i => match i with
        | Sum.inl w => p.1 w
        | Sum.inr v => p.2 v
      left_inv := fun y => by funext i; cases i <;> rfl
      right_inv := fun p => by rfl }
  have he : DenseRange e := e.surjective.denseRange
  have h1 : DenseRange (Pi.map fun (w : InfinitePlace K) (x : WithAbs w.1) => (x : w.Completion)) :=
    DenseRange.piMap fun w => NumberField.InfinitePlace.Completion.denseRange_coe w
  have h2 : DenseRange (Pi.map fun (v : ↥S) (y : WithAbs (NumberField.HeightOneSpectrum.adicAbv K v.1)) =>
      algebraMap K (v.1.adicCompletion K) (WithAbs.equiv (NumberField.HeightOneSpectrum.adicAbv K v.1) y)) := by
    refine DenseRange.piMap fun v => ?_
    have := IsDedekindDomain.HeightOneSpectrum.denseRange_algebraMap (K := K) v.1

    intro x
    have hx := this x
    rw [mem_closure_iff_nhds] at hx ⊢
    intro t ht
    obtain ⟨y, hyt, ⟨k, rfl⟩⟩ := hx t ht
    exact ⟨_, hyt, ⟨(WithAbs.equiv (NumberField.HeightOneSpectrum.adicAbv K v.1)).symm k, by simp⟩⟩
  have h12 := h1.prodMap h2
  have : toMixed K S = (Prod.map (Pi.map fun (w : InfinitePlace K) (x : WithAbs w.1) => (x : w.Completion))
      (Pi.map fun (v : ↥S) (y : WithAbs (NumberField.HeightOneSpectrum.adicAbv K v.1)) =>
        algebraMap K (v.1.adicCompletion K) (WithAbs.equiv (NumberField.HeightOneSpectrum.adicAbv K v.1) y))) ∘ e := by
    funext y
    refine Prod.ext ?_ ?_
    · funext w
      rfl
    · funext v
      rfl
  rw [this]
  exact h12.comp he ((Continuous.prodMap (continuous_pi fun w =>
    (NumberField.InfinitePlace.Completion.continuous_coe _).comp (continuous_apply _))
    (continuous_pi fun v => (continuous_adicCompletion_of_withAbs K v.1).comp (continuous_apply _))))

theorem denseRange_mixedEmb (S : Finset (HeightOneSpectrum (𝓞 K))) : DenseRange (mixedEmb K S) := by
  exact (denseRange_toMixed K S).comp (denseRange_algebraMap_pi_withAbs K S) (continuous_toMixed K S)

end NumberField.WeakApprox

theorem solution
    (K : Type*) [Field K] [NumberField K] (S : Finset (HeightOneSpectrum (𝓞 K))) :
    DenseRange fun x : K =>
      (algebraMap K (InfiniteAdeleRing K) x, fun v : ↥S => algebraMap K (v.1.adicCompletion K) x) :=
  NumberField.WeakApprox.denseRange_mixedEmb K S

end S_NumberField_denseRange_algebraMap_infiniteAdeleRing_prod_adicCompletion
end P2MW
export P2MW.S_NumberField_denseRange_algebraMap_infiniteAdeleRing_prod_adicCompletion (solution)
