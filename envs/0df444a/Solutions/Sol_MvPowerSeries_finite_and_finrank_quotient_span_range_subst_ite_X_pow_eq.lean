-- Prove2me | solution 1 for MvPowerSeries.finite_and_finrank_quotient_span_range_subst_ite_X_pow_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/df77a07e-f448-5641-835a-7843e993d2e3

import Mathlib
import Theorems.Thm_MvPowerSeries_finite_flat_exists_basis_substAlgHom_of_finite_quotient
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MvPowerSeries_finite_and_finrank_quotient_span_range_subst_ite_X_pow_eq
p2m_attr_erase "instance" "instTopologicallyFGOfFiniteType"

set_option autoImplicit false

noncomputable section

universe u

namespace P2mKcPartialFrobFree

open MvPowerSeries

variable {k : Type u} [Field k] {d : ℕ} (T : Finset (Fin d)) (q : ℕ)

local notation "A" => MvPowerSeries (Fin d) k

def E : Fin d → A := fun j => if j ∈ T then X j else X j ^ q

def w (j : Fin d) : ℕ := if j ∈ T then 1 else q

variable {T q}

theorem E_eq_X_pow (j : Fin d) : E (k := k) T q j = X j ^ w T q j := by
  unfold E w
  split_ifs <;> simp

theorem constantCoeff_E (hq : 0 < q) (j : Fin d) : (E (k := k) T q j).constantCoeff = 0 := by
  rw [E_eq_X_pow, map_pow, constantCoeff_X, zero_pow]
  unfold w; split_ifs
  · exact one_ne_zero
  · exact hq.ne'

theorem hasSubst_E (hq : 0 < q) : HasSubst (E (k := k) T q) :=
  hasSubst_of_constantCoeff_zero (constantCoeff_E hq)

theorem w_pos (hq : 0 < q) (j : Fin d) : 0 < w T q j := by
  unfold w; split_ifs
  · exact one_pos
  · exact hq

abbrev Box (T : Finset (Fin d)) (q : ℕ) := {j : Fin d // j ∉ T} → Fin q

def toExp (v : Box T q) : Fin d →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun j => if h : j ∈ T then 0 else (v ⟨j, h⟩ : ℕ)

@[scoped simp] theorem toExp_apply (v : Box T q) (j : Fin d) :
    toExp v j = if h : j ∈ T then 0 else (v ⟨j, h⟩ : ℕ) := by
  simp [toExp]

theorem toExp_lt_w (v : Box T q) (j : Fin d) : toExp v j < w T q j := by
  rw [toExp_apply]
  unfold w
  split_ifs with h
  · exact one_pos
  · exact (v ⟨j, h⟩).isLt

def boxCoeff : A →ₗ[k] (Box T q → k) where
  toFun f v := coeff (toExp v) f
  map_add' f g := by funext v; simp
  map_smul' c f := by funext v; simp

theorem boxCoeff_apply (f : A) (v : Box T q) : boxCoeff (T := T) (q := q) f v = coeff (toExp v) f := rfl

theorem boxCoeff_surjective : Function.Surjective (boxCoeff (k := k) (T := T) (q := q)) := by
  intro u
  classical
  refine ⟨fun m => if h : ∀ j (hj : j ∉ T), m j < q then u (fun jj => ⟨m jj.1, h jj.1 jj.2⟩) else 0, ?_⟩
  funext v
  rw [boxCoeff_apply]
  show (if h : ∀ j (hj : j ∉ T), toExp v j < q then u (fun jj => ⟨toExp v jj.1, h jj.1 jj.2⟩) else 0) = u v
  have hv : ∀ j (hj : j ∉ T), toExp v j < q := fun j hj => by
    rw [toExp_apply, dif_neg hj]; exact (v ⟨j, hj⟩).isLt
  rw [dif_pos hv]
  congr 1
  funext jj
  ext
  simp [toExp_apply, jj.2]

def bad (m : Fin d →₀ ℕ) (j : Fin d) : Prop := w T q j ≤ m j

scoped instance (m : Fin d →₀ ℕ) : DecidablePred (bad (T := T) (q := q) m) := fun j => by
  unfold bad; infer_instance

theorem exists_toExp_eq_of_forall_not_bad (m : Fin d →₀ ℕ) (hm : ∀ j, ¬ bad (T := T) (q := q) m j) :
    ∃ v : Box T q, toExp v = m := by
  refine ⟨fun jj => ⟨m jj.1, ?_⟩, ?_⟩
  · have h := hm jj.1
    unfold bad w at h
    rw [if_neg jj.2] at h
    omega
  · ext j
    rw [toExp_apply]
    by_cases h : j ∈ T
    · rw [dif_pos h]
      have h' := hm j
      unfold bad w at h'
      rw [if_pos h] at h'
      omega
    · rw [dif_neg h]

theorem ker_boxCoeff (_hq : 0 < q) :
    LinearMap.ker (boxCoeff (k := k) (T := T) (q := q)) = (Ideal.span (Set.range (E (k := k) T q))).restrictScalars k := by
  classical
  apply le_antisymm
  ·
    intro f hf
    rw [LinearMap.mem_ker] at hf
    have hf' : ∀ m : Fin d →₀ ℕ, (∀ j, ¬ bad (T := T) (q := q) m j) → coeff m f = 0 := by
      intro m hm
      obtain ⟨v, rfl⟩ := exists_toExp_eq_of_forall_not_bad m hm
      exact congrFun hf v

    let h : Fin d → A := fun j n =>
      if hb : ∃ i, bad (T := T) (q := q) (n + Finsupp.single j (w T q j)) i then
        (if Fin.find _ hb = j then coeff (n + Finsupp.single j (w T q j)) f else 0)
      else 0
    have hdec : f = ∑ j, E T q j * h j := by
      ext m
      rw [map_sum]
      have hterm : ∀ j, coeff m (E T q j * h j) =
          if hb : ∃ i, bad (T := T) (q := q) m i then (if Fin.find _ hb = j then coeff m f else 0) else 0 := by
        intro j
        rw [E_eq_X_pow, X_pow_eq, coeff_monomial_mul, one_mul]
        by_cases hle : Finsupp.single j (w T q j) ≤ m
        · rw [if_pos hle]
          have hmn : m - Finsupp.single j (w T q j) + Finsupp.single j (w T q j) = m := tsub_add_cancel_of_le hle
          show (if hb : ∃ i, bad (T := T) (q := q) (m - Finsupp.single j (w T q j) + Finsupp.single j (w T q j)) i
            then (if Fin.find _ hb = j then coeff (m - Finsupp.single j (w T q j) + Finsupp.single j (w T q j)) f else 0)
            else 0) = _
          rw [hmn]
        · rw [if_neg hle]
          split_ifs with hb hj
          · exfalso
            apply hle
            rw [Finsupp.single_le_iff]
            have := Fin.find_spec hb
            rw [hj] at this
            exact this
          · rfl
          · rfl
      simp only [hterm]
      by_cases hb : ∃ i, bad (T := T) (q := q) m i
      · simp only [dif_pos hb]
        rw [Finset.sum_ite_eq, if_pos (Finset.mem_univ _)]
      · simp only [dif_neg hb, Finset.sum_const_zero]
        push Not at hb
        exact hf' m hb
    rw [hdec]
    refine Submodule.sum_mem _ fun j _ => ?_
    show E T q j * h j ∈ Ideal.span (Set.range (E T q))
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨j, rfl⟩)
  ·
    intro f hf
    change f ∈ Ideal.span (Set.range (E T q)) at hf
    rw [LinearMap.mem_ker]
    funext v
    rw [boxCoeff_apply, Pi.zero_apply]
    obtain ⟨c, rfl⟩ := Ideal.mem_span_range_iff_exists_fun.mp hf
    rw [map_sum]
    refine Finset.sum_eq_zero fun j _ => ?_
    have hdvd : (X j : A) ^ w T q j ∣ c j * E T q j := by
      rw [E_eq_X_pow]; exact Dvd.intro_left _ rfl
    exact (X_pow_dvd_iff.mp hdvd) _ (toExp_lt_w v j)

def quotSpanEEquiv (hq : 0 < q) : (A ⧸ Ideal.span (Set.range (E (k := k) T q))) ≃ₗ[k] (Box T q → k) :=
  (Submodule.Quotient.restrictScalarsEquiv k (Ideal.span (Set.range (E (k := k) T q)))).symm.trans
    ((Submodule.quotEquivOfEq _ _ (ker_boxCoeff hq).symm).trans
      (LinearMap.quotKerEquivOfSurjective _ boxCoeff_surjective))

theorem card_box : Fintype.card (Box T q) = q ^ (d - T.card) := by
  classical
  rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_subtype_compl, Fintype.card_fin]
  congr 2
  exact Fintype.card_coe T

theorem finrank_quotient_span_E (hq : 0 < q) :
    Module.finrank k (A ⧸ Ideal.span (Set.range (E (k := k) T q))) = q ^ (d - T.card) := by
  rw [(quotSpanEEquiv hq).finrank_eq, Module.finrank_fintype_fun_eq_card, card_box]

theorem finite_quotient_span_E (hq : 0 < q) :
    Module.Finite k (A ⧸ Ideal.span (Set.range (E (k := k) T q))) :=
  Module.Finite.equiv (quotSpanEEquiv hq).symm

def coordMap (T : Finset (Fin d)) (q : ℕ) (hq : 0 < q) {N : ℕ} (b : Fin N → A) : (Fin N → A) →ₗ[k] A where
  toFun c := ∑ i, subst (E (k := k) T q) (c i) * b i
  map_add' c c' := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Pi.add_apply, subst_add (hasSubst_E hq), add_mul]
  map_smul' r c := by
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Pi.smul_apply, subst_smul (hasSubst_E hq), RingHom.id_apply, smul_mul_assoc]

theorem coordMap_apply (hq : 0 < q) {N : ℕ} (b : Fin N → A) (c : Fin N → A) :
    coordMap T q hq b c = ∑ i, subst (E (k := k) T q) (c i) * b i := rfl

theorem main (hq : 0 < q) (g : Fin d → A) (_hg : ∀ i, (g i).constantCoeff = 0) :
    (Module.Finite k (A ⧸ Ideal.span (Set.range fun i => subst (E (k := k) T q) (g i))) ↔
      Module.Finite k (A ⧸ Ideal.span (Set.range g))) ∧
    Module.finrank k (A ⧸ Ideal.span (Set.range fun i => subst (E (k := k) T q) (g i))) =
      q ^ (d - T.card) * Module.finrank k (A ⧸ Ideal.span (Set.range g)) := by
  classical

  haveI := finite_quotient_span_E (k := k) (T := T) hq
  obtain ⟨-, -, b, hb⟩ := MvPowerSeries.finite_flat_exists_basis_substAlgHom_of_finite_quotient
    (E (k := k) T q) (constantCoeff_E hq) inferInstance
  have hNq : Module.finrank k (A ⧸ Ideal.span (Set.range (E (k := k) T q))) = q ^ (d - T.card) :=
    finrank_quotient_span_E hq
  generalize Module.finrank k (A ⧸ Ideal.span (Set.range (E (k := k) T q))) = N at b hb hNq
  have hN1 : 0 < N := by rw [hNq]; exact pow_pos hq _

  have hsubst : ∀ x, MvPowerSeries.substAlgHom (R := k)
      (MvPowerSeries.hasSubst_of_constantCoeff_zero (constantCoeff_E (k := k) (T := T) hq)) x = subst (E T q) x :=
    fun x => substAlgHom_apply _ x
  have hb' : ∀ x : A, ∃! c : Fin N → A, x = coordMap T q hq b c := by
    intro x
    obtain ⟨c, hc, huniq⟩ := hb x
    refine ⟨c, ?_, fun c' hc' => huniq c' ?_⟩
    · show x = coordMap T q hq b c
      rw [coordMap_apply]; simpa only [hsubst] using hc
    · change x = coordMap T q hq b c' at hc'
      show x = ∑ i, _
      rw [coordMap_apply] at hc'; simpa only [hsubst] using hc'
  have hinj : Function.Injective (coordMap (k := k) T q hq b) := by
    intro c c' h
    obtain ⟨c₀, -, huniq⟩ := hb' (coordMap T q hq b c)
    exact (huniq c rfl).trans (huniq c' h).symm
  have hsurj : Function.Surjective (coordMap (k := k) T q hq b) := by
    intro x
    obtain ⟨c, hc, -⟩ := hb' x
    exact ⟨c, hc.symm⟩
  let eΘ : (Fin N → A) ≃ₗ[k] A := LinearEquiv.ofBijective _ ⟨hinj, hsurj⟩
  have eΘ_apply : ∀ c, eΘ c = ∑ i, subst (E (k := k) T q) (c i) * b i := fun c => rfl

  set J : Ideal A := Ideal.span (Set.range g) with hJ
  set J' : Ideal A := Ideal.span (Set.range fun i => subst (E (k := k) T q) (g i)) with hJ'
  let JN : Submodule k (Fin N → A) := Submodule.pi Set.univ fun _ => J.restrictScalars k
  have hE := hasSubst_E (k := k) (T := T) hq

  have hEJ : ∀ y ∈ J, subst (E (k := k) T q) y ∈ J' := by
    intro y hy
    obtain ⟨a, rfl⟩ := Ideal.mem_span_range_iff_exists_fun.mp hy
    rw [← coe_substAlgHom hE, map_sum]
    refine Ideal.sum_mem _ fun l _ => ?_
    rw [map_mul]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨l, (substAlgHom_apply hE _).symm⟩)
  have hmap : JN.map (eΘ : (Fin N → A) →ₗ[k] A) = J'.restrictScalars k := by
    apply le_antisymm
    · rintro _ ⟨c, hc, rfl⟩
      change eΘ c ∈ J'
      rw [eΘ_apply]
      refine Ideal.sum_mem _ fun i _ => Ideal.mul_mem_right _ _ (hEJ _ ?_)
      exact hc i (Set.mem_univ i)
    · intro y hy
      change y ∈ J' at hy
      obtain ⟨a, rfl⟩ := Ideal.mem_span_range_iff_exists_fun.mp hy
      refine Submodule.sum_mem _ fun l _ => ?_
      obtain ⟨c, hc⟩ := hsurj (a l)
      have hcl : (fun i => c i * g l) ∈ JN := fun i _ =>
        show c i * g l ∈ J from Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨l, rfl⟩)
      refine ⟨fun i => c i * g l, hcl, ?_⟩
      change eΘ (fun i => c i * g l) = a l * subst (E (k := k) T q) (g l)
      rw [eΘ_apply, ← hc, coordMap_apply, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [subst_mul hE]
      ring

  let e : (A ⧸ J') ≃ₗ[k] (Fin N → A ⧸ J) :=
    (Submodule.Quotient.restrictScalarsEquiv k J').symm.trans
      ((Submodule.Quotient.equiv JN (J'.restrictScalars k) eΘ hmap).symm.trans
        ((Submodule.quotientPi fun _ : Fin N => J.restrictScalars k).trans
          (LinearEquiv.piCongrRight fun _ => Submodule.Quotient.restrictScalarsEquiv k J)))

  have hfin_iff : Module.Finite k (A ⧸ J') ↔ Module.Finite k (A ⧸ J) := by
    constructor
    · intro hfin
      haveI : Module.Finite k (Fin N → A ⧸ J) := Module.Finite.equiv e
      exact Module.Finite.of_surjective (LinearMap.proj (⟨0, hN1⟩ : Fin N) : (Fin N → A ⧸ J) →ₗ[k] A ⧸ J)
        (LinearMap.proj_surjective _)
    · intro hfin
      haveI : Module.Finite k (Fin N → A ⧸ J) := Module.Finite.pi
      exact Module.Finite.equiv e.symm
  refine ⟨hfin_iff, ?_⟩
  rw [e.finrank_eq, ← hNq]
  by_cases hfin : Module.Finite k (A ⧸ J)
  · rw [Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  · have h1 : ¬ Module.Finite k (Fin N → A ⧸ J) := fun h => hfin (by
      haveI := h
      exact Module.Finite.of_surjective (LinearMap.proj (⟨0, hN1⟩ : Fin N) : (Fin N → A ⧸ J) →ₗ[k] A ⧸ J)
        (LinearMap.proj_surjective _))
    rw [Module.finrank_of_not_finite h1, Module.finrank_of_not_finite hfin, mul_zero]

end P2mKcPartialFrobFree
p2m_reactivate "P2MW.S_MvPowerSeries_finite_and_finrank_quotient_span_range_subst_ite_X_pow_eq.P2mKcPartialFrobFree"

open P2mKcPartialFrobFree MvPowerSeries in

theorem solution
    {k : Type u} [Field k] {d : ℕ} (T : Finset (Fin d)) (q : ℕ) (hq : 0 < q)
    (g : Fin d → MvPowerSeries (Fin d) k) (hg : ∀ i, (g i).constantCoeff = 0) :
    (Module.Finite k (MvPowerSeries (Fin d) k ⧸ Ideal.span (Set.range fun i =>
        subst (fun j => if j ∈ T then (X j : MvPowerSeries (Fin d) k) else X j ^ q) (g i))) ↔
      Module.Finite k (MvPowerSeries (Fin d) k ⧸ Ideal.span (Set.range g))) ∧
    Module.finrank k (MvPowerSeries (Fin d) k ⧸ Ideal.span (Set.range fun i =>
        subst (fun j => if j ∈ T then (X j : MvPowerSeries (Fin d) k) else X j ^ q) (g i))) =
      q ^ (d - T.card) *
        Module.finrank k (MvPowerSeries (Fin d) k ⧸ Ideal.span (Set.range g)) :=
  main hq g hg

end
p2m_reactivate "P2MW.S_MvPowerSeries_finite_and_finrank_quotient_span_range_subst_ite_X_pow_eq.P2mKcPartialFrobFree"

end S_MvPowerSeries_finite_and_finrank_quotient_span_range_subst_ite_X_pow_eq
end P2MW
export P2MW.S_MvPowerSeries_finite_and_finrank_quotient_span_range_subst_ite_X_pow_eq (solution)
