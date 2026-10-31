-- Prove2me | solution 1 for MinBuying.sorted_pmf_mass
-- status  : ACCEPTED   (prove)
-- author  : @mikeh
-- created : 2026-10-30T18:09:39.77161+00:00
-- url     : https://prove2.me/submissions/ab977698-2a15-48ae-bacf-4c16cfb52ea0

import Definitions.Def_MinBuying_Symmetry

open MeasureTheory Set MinBuying
open scoped BigOperators ENNReal NNReal

noncomputable section

private lemma pmf_invariant {n : ℕ} (w : PMF (Valuations n))
    (hex : Exchangeable w.toMeasure) (σ : Equiv.Perm (Fin n)) (v : Valuations n) :
    w (v ∘ σ) = w v := by
  classical
  have hm : Measurable (permuteCoordinates σ) := by
    apply measurable_pi_iff.mpr
    intro i
    exact measurable_pi_apply (σ i)
  have heq : w.map (permuteCoordinates σ) = w :=
    PMF.toMeasure_injective ((PMF.toMeasure_map (permuteCoordinates σ) w hm).symm.trans (hex σ))
  have hinj : Function.Injective (permuteCoordinates σ) := by
    intro a b hab
    funext i
    have hh := congrFun hab (σ.symm i)
    simpa [permuteCoordinates] using hh
  have hmass : (w.map (permuteCoordinates σ)) (permuteCoordinates σ v) = w v := by
    simp [PMF.map_apply,hinj.eq_iff]
  rw [heq] at hmass
  exact hmass

private lemma sorted_eq_iff_orbit {n : ℕ} (v z : Valuations n) (hv : Monotone v) :
    z ∘ Tuple.sort z = v ↔
      z ∈ MulAction.orbit (Equiv.Perm (Fin n))ᵈᵐᵃ v := by
  constructor
  · intro h
    apply MulAction.mem_orbit_iff.mpr
    refine ⟨DomMulAct.mk (Tuple.sort z).symm,?_⟩
    change v ∘ (Tuple.sort z).symm = z
    funext i
    have hh := congrFun h ((Tuple.sort z).symm i)
    simpa using hh.symm
  · intro h
    obtain ⟨g,rfl⟩ := MulAction.mem_orbit_iff.mp h
    change (v ∘ (DomMulAct.mk.symm g : Equiv.Perm (Fin n))) ∘
      Tuple.sort (v ∘ (DomMulAct.mk.symm g : Equiv.Perm (Fin n))) = v
    rw [Tuple.comp_perm_comp_sort_eq_comp_sort,
      Tuple.sort_eq_refl_iff_monotone.mpr hv]
    rfl

private lemma orbit_size {n : ℕ} (v : Valuations n)
    [Fintype (MulAction.orbit (Equiv.Perm (Fin n))ᵈᵐᵃ v)] :
    (Fintype.card (MulAction.orbit (Equiv.Perm (Fin n))ᵈᵐᵃ v) : ℝ) =
      (n.factorial : ℝ) /
        (∏ x ∈ Finset.univ.image v,
          (((Finset.univ.filter (fun i : Fin n => v i = x)).card).factorial : ℝ)) := by
  classical
  let G := (Equiv.Perm (Fin n))ᵈᵐᵃ
  letI : Fintype G := Fintype.ofEquiv (Equiv.Perm (Fin n)) DomMulAct.mk
  letI : Fintype (MulAction.stabilizer G v) := Fintype.ofFinite _
  have hstab : Fintype.card (MulAction.stabilizer G v) =
      ∏ x ∈ Finset.univ.image v,
        ((Finset.univ.filter (fun i : Fin n => v i = x)).card).factorial := by
    calc
      Fintype.card (MulAction.stabilizer G v) =
          Fintype.card {σ : Equiv.Perm (Fin n) // v ∘ σ = v} :=
        Fintype.card_congr (Equiv.subtypeEquiv DomMulAct.mk.symm
          (fun _ => DomMulAct.mem_stabilizer_iff))
      _ = _ := by
        rw [DomMulAct.stabilizer_card']
        simp only [Fintype.card_subtype]
  have hG : Fintype.card G = n.factorial := by
    rw [Fintype.card_congr DomMulAct.mk.symm,Fintype.card_perm,Fintype.card_fin]
  have hcard := MulAction.card_orbit_mul_card_stabilizer_eq_card_group G v
  rw [hstab,hG] at hcard
  have hden : 0 < (∏ x ∈ Finset.univ.image v,
      (((Finset.univ.filter (fun i : Fin n => v i = x)).card).factorial : ℝ)) := by
    exact Finset.prod_pos (fun x hx => Nat.cast_pos.mpr (Nat.factorial_pos _))
  apply (eq_div_iff hden.ne').mpr
  exact_mod_cast hcard

theorem solution (n : ℕ) (w : PMF (Valuations n))
    (hex : Exchangeable w.toMeasure) :
    ∀ v : Valuations n,
      (Monotone v →
        ((w.map (fun z => z ∘ Tuple.sort z)) v).toReal =
          ((n.factorial : ℝ) /
            (∏ x ∈ Finset.univ.image v,
              (((Finset.univ.filter (fun i : Fin n => v i = x)).card).factorial : ℝ))) *
            (w v).toReal) ∧
      (¬ Monotone v → (w.map (fun z => z ∘ Tuple.sort z)) v = 0) := by
  classical
  intro v
  constructor
  · intro hv
    let G := (Equiv.Perm (Fin n))ᵈᵐᵃ
    letI : Fintype G := Fintype.ofEquiv (Equiv.Perm (Fin n)) DomMulAct.mk
    have hfin : Set.Finite (MulAction.orbit G v) := Set.finite_range (fun g : G => g • v)
    letI : Fintype (MulAction.orbit G v) := hfin.fintype
    have hmass : (w.map (fun z => z ∘ Tuple.sort z)) v =
        (Fintype.card (MulAction.orbit G v) : ℝ≥0∞) * w v := by
      rw [PMF.map_apply]
      calc
        _ = ∑' z : MulAction.orbit G v, w z := by
          rw [tsum_subtype]
          apply tsum_congr
          intro z
          have hh := sorted_eq_iff_orbit v z hv
          simp only [Set.indicator_apply]
          by_cases hz : z ∈ MulAction.orbit G v
          · have heq : v = z ∘ Tuple.sort z := (hh.mpr hz).symm
            simp only [if_pos hz,if_pos heq]
          · have hne : v ≠ z ∘ Tuple.sort z := fun h => hz (hh.mp h.symm)
            simp only [if_neg hz,if_neg hne]
        _ = ∑' _z : MulAction.orbit G v, w v := by
          apply tsum_congr
          intro z
          obtain ⟨g,hg⟩ := MulAction.mem_orbit_iff.mp z.property
          rw [← hg]
          exact pmf_invariant w hex (DomMulAct.mk.symm g) v
        _ = _ := by simp [tsum_fintype,nsmul_eq_mul]
    rw [hmass,ENNReal.toReal_mul,ENNReal.toReal_natCast,orbit_size v]
  · intro hv
    rw [PMF.map_apply]
    apply ENNReal.tsum_eq_zero.mpr
    intro z
    have hne : v ≠ z ∘ Tuple.sort z := fun h => hv (h.symm ▸ Tuple.monotone_sort z)
    simp [hne]
