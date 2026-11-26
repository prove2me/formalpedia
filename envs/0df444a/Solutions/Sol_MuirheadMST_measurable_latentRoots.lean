-- Prove2me | solution 1 for MuirheadMST.measurable_latentRoots
-- status  : ACCEPTED   (prove)
-- author  : @domodus
-- created : 2026-11-26T21:07:51.313008+00:00
-- url     : https://prove2.me/submissions/c75fedd9-2594-4c44-82b8-dfca81690096

import Mathlib
import Definitions.Def_MuirheadMST_Wishart

open MeasureTheory Polynomial

namespace MuirheadMST.MeasurableLatentRoots

/-- Values `n ↦ ∏ i, (n - l i)` of the monic polynomial with roots `l` at the naturals. -/
noncomputable def evalNat {m : ℕ} (l : Fin m → ℝ) : ℕ → ℝ := fun n => ∏ i, ((n : ℝ) - l i)

/-- The monic polynomial with roots `l`. -/
noncomputable def rootPoly {m : ℕ} (l : Fin m → ℝ) : ℝ[X] :=
  ((Finset.univ.val.map l).map fun a => X - C a).prod

lemma eval_rootPoly {m : ℕ} (l : Fin m → ℝ) (x : ℝ) : (rootPoly l).eval x = ∏ i, (x - l i) := by
  rw [rootPoly, eval_multiset_prod, Multiset.map_map, Multiset.map_map, Finset.prod_eq_multiset_prod]
  simp [Function.comp_def]

lemma degree_rootPoly_lt {m : ℕ} (l : Fin m → ℝ) : (rootPoly l).degree < (m + 1 : ℕ) := by
  refine degree_le_natDegree.trans_lt ?_
  rw [rootPoly, natDegree_multiset_prod_X_sub_C_eq_card]
  simp only [Multiset.card_map, Finset.card_val, Finset.card_univ, Fintype.card_fin]
  exact_mod_cast Nat.lt_succ_self m

/-- An antitone vector is determined by the values of its root polynomial at the naturals. -/
lemma evalNat_injOn {m : ℕ} {l l' : Fin m → ℝ} (hl : Antitone l) (hl' : Antitone l')
    (h : evalNat l = evalNat l') : l = l' := by
  have hp : rootPoly l = rootPoly l' := by
    let s : Finset ℝ := (Finset.range (m + 1)).image (Nat.cast : ℕ → ℝ)
    have hs : s.card = m + 1 := by
      rw [Finset.card_image_of_injective _ Nat.cast_injective, Finset.card_range]
    refine eq_of_degrees_lt_of_eval_finset_eq s (hs ▸ degree_rootPoly_lt l)
      (hs ▸ degree_rootPoly_lt l') ?_
    intro x hx
    obtain ⟨n, -, rfl⟩ := Finset.mem_image.mp hx
    rw [eval_rootPoly, eval_rootPoly]
    exact congrFun h n
  have hr : Finset.univ.val.map l = Finset.univ.val.map l' := by
    have := congrArg Polynomial.roots hp
    rwa [rootPoly, rootPoly, roots_multiset_prod_X_sub_C, roots_multiset_prod_X_sub_C] at this
  rw [Fin.univ_val_map, Fin.univ_val_map, Multiset.coe_eq_coe] at hr
  exact List.ofFn_inj.mp (hr.eq_of_sortedGE hl.sortedGE_ofFn hl'.sortedGE_ofFn)

lemma evalNat_latentRoots {m : ℕ} (A : Fin m → Fin m → ℝ) (hA : (Matrix.of A).IsHermitian) :
    evalNat (latentRoots A) = fun n : ℕ => ((Matrix.of A).charpoly).eval (n : ℝ) := by
  funext n
  rw [hA.charpoly_eq, eval_prod, evalNat, latentRoots, dif_pos hA]
  simp only [eval_sub, eval_X, eval_C, Matrix.IsHermitian.eigenvalues, RCLike.ofReal_real_eq_id, id]
  exact (Equiv.prod_comp (finCongr (Fintype.card_fin m).symm)
    (fun k => (n : ℝ) - hA.eigenvalues₀ k)).trans
    (Equiv.prod_comp (Fintype.equivOfCardEq (Fintype.card_fin _)).symm
      (fun k => (n : ℝ) - hA.eigenvalues₀ k)).symm

lemma latentRoots_antitone {m : ℕ} (A : Fin m → Fin m → ℝ) (hA : (Matrix.of A).IsHermitian) :
    Antitone (latentRoots A) := by
  rw [latentRoots, dif_pos hA]
  exact hA.eigenvalues₀_antitone.comp_monotone fun a b h => h

end MuirheadMST.MeasurableLatentRoots

open MuirheadMST MuirheadMST.MeasurableLatentRoots

theorem solution (m : ℕ) :
    Measurable (latentRoots : (Fin m → Fin m → ℝ) → Fin m → ℝ) := by
  let S : Set (Fin m → ℝ) := {l | Antitone l}
  have hS : IsClosed S := isClosed_antitone
  haveI := hS.polishSpace
  have hcont : Continuous fun l : S => evalNat l.1 := by
    exact continuous_pi fun n => continuous_finset_prod _ fun i _ =>
      continuous_const.sub ((continuous_apply i).comp continuous_subtype_val)
  have hemb : MeasurableEmbedding fun l : S => evalNat l.1 :=
    hcont.measurableEmbedding fun a b h => Subtype.ext (evalNat_injOn a.2 b.2 h)
  obtain ⟨g, hg, hgψ⟩ := hemb.exists_measurable_extend measurable_subtype_coe fun _ => ⟨0⟩
  let H : Set (Fin m → Fin m → ℝ) := {A | (Matrix.of A).IsHermitian}
  have hH : MeasurableSet H := by
    have : H = ⋂ i, ⋂ j, {A | A j i = A i j} := by
      ext A
      simp [H, Matrix.IsHermitian, ← Matrix.ext_iff, Matrix.conjTranspose_apply]
    rw [this]
    exact MeasurableSet.iInter fun i => MeasurableSet.iInter fun j =>
      measurableSet_eq_fun (by fun_prop) (by fun_prop)
  have hc : Measurable fun A : Fin m → Fin m → ℝ => fun n : ℕ => ((Matrix.of A).charpoly).eval (n : ℝ) := by
    refine measurable_pi_lambda _ fun n => ?_
    simp_rw [Matrix.eval_charpoly]
    refine Continuous.measurable ?_
    exact (continuous_const.sub (continuous_id (X := Matrix (Fin m) (Fin m) ℝ))).matrix_det
  have key : (latentRoots : (Fin m → Fin m → ℝ) → Fin m → ℝ) =
      fun A => if A ∈ H then g (fun n : ℕ => ((Matrix.of A).charpoly).eval (n : ℝ)) else 0 := by
    funext A
    by_cases hA : A ∈ H
    · rw [if_pos hA, ← evalNat_latentRoots A hA]
      exact (congrFun hgψ ⟨latentRoots A, latentRoots_antitone A hA⟩).symm
    · rw [if_neg hA]
      exact dif_neg hA
  rw [key]
  exact Measurable.ite hH (hg.comp hc) measurable_const
