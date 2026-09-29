-- Prove2me | solution 1 for MTT.Eigenform.coefficientField_finiteDimensional
-- status  : ACCEPTED   (prove)
-- author  : @davidloeffler
-- created : 2026-09-20T10:14:40.816124+00:00
-- url     : https://prove2.me/submissions/bbc2c9d9-d7f1-47de-9171-b686f5e8a52e

import Definitions.Def_MTT_EigenformCoefficientField
import Theorems.Thm_MTT_Cohomology_eigenform_uniform_hecke_stable_period_lattice
import Theorems.Thm_MTT_Eigenform_hecke_recurrence
import Mathlib.Algebra.Algebra.Hom.Rat

set_option autoImplicit false
noncomputable section

namespace CoefficientFieldFinite

/-- Scalars preserving a fixed integral lattice. -/
def scalarStabilizer (L : Submodule ℤ MTT.Qbar) : Subring MTT.Qbar where
  carrier := {a | ∀ x, x ∈ L → a * x ∈ L}
  zero_mem' := by simp
  one_mem' := by simp
  add_mem' := by
    intro a b ha hb x hx
    simpa [add_mul] using L.add_mem (ha x hx) (hb x hx)
  neg_mem' := by
    intro a ha x hx
    simpa using L.neg_mem (ha x hx)
  mul_mem' := by
    intro a b ha hb x hx
    simpa [mul_assoc] using ha (b * x) (hb x hx)

theorem scalarStabilizer_moduleFinite
    (L : Submodule ℤ MTT.Qbar) (hne : L ≠ ⊥) (hfg : L.FG) :
    Module.Finite ℤ (scalarStabilizer L) := by
  rw [Ne, Submodule.eq_bot_iff] at hne
  push Not at hne
  obtain ⟨x, hxL, hx0⟩ := hne
  let F : scalarStabilizer L →ₗ[ℤ] L :=
    { toFun := fun a => ⟨a.1 * x, a.2 x hxL⟩
      map_add' := by
        intro a b
        ext
        simp [add_mul]
      map_smul' := by
        intro a b
        ext
        simp [mul_assoc] }
  have hFi : Function.Injective F := by
    intro a b hab
    apply Subtype.ext
    have hv := congrArg Subtype.val hab
    exact mul_right_cancel₀ hx0 hv
  haveI : Module.Finite ℤ L := Module.Finite.iff_fg.mpr hfg
  exact Module.Finite.of_injective F hFi

theorem _root_.solution
    {N k : ℕ} (hN : 0 < N) (hk : 2 ≤ k)
    (ι : MTT.Qbar →+* ℂ) (f : MTT.Eigenform N k ι) :
    FiniteDimensional ℚ f.coefficientField := by
  obtain ⟨ψ, hpacket, hLne, hLfg, hstable⟩ :=
    MTT.Cohomology.eigenform_uniform_hecke_stable_period_lattice hN hk ι f
  let L : Submodule ℤ MTT.Qbar :=
    Submodule.span ℤ {v : MTT.Qbar | ∃ s j r, j ≤ k - 2 ∧
      v = MTT.Cohomology.evaluation j r (ψ s) /
        ((k - 2).choose j : MTT.Qbar)}
  let A : Subring MTT.Qbar := scalarStabilizer L
  have hAfin : Module.Finite ℤ A :=
    scalarStabilizer_moduleFinite L hLne hLfg
  letI : Module.Finite ℤ A := hAfin
  obtain ⟨d, gen, hgen⟩ := Module.Finite.exists_fin (R := ℤ) (M := A)
  let T : Set MTT.Qbar :=
    Set.range (fun i : Fin d => (gen i : MTT.Qbar)) ∪ Set.range f.epsilon
  let K : Subfield MTT.Qbar := (IntermediateField.adjoin ℚ T).toSubfield
  let _ : Algebra.IsAlgebraic ℚ MTT.Qbar := AlgebraicClosure.isAlgebraic ℚ
  haveI : NeZero N := ⟨Nat.ne_of_gt hN⟩
  have hTfinite : T.Finite :=
    (Set.finite_range (fun i : Fin d => (gen i : MTT.Qbar))).union
      (Set.finite_range f.epsilon)
  letI : Fintype T := hTfinite.fintype
  haveI : FiniteDimensional ℚ K := by
    change FiniteDimensional ℚ (IntermediateField.adjoin ℚ T)
    exact IntermediateField.finiteDimensional_adjoin
      (fun x _ => Algebra.IsIntegral.isIntegral x)
  have hAK : (A : Set MTT.Qbar) ⊆ K := by
    intro a ha
    let aa : A := ⟨a, ha⟩
    change (aa : MTT.Qbar) ∈ K
    have haa : aa ∈ Submodule.span ℤ (Set.range gen) := by
      rw [hgen]
      trivial
    refine Submodule.span_induction
      (p := fun z (_ : z ∈ Submodule.span ℤ (Set.range gen)) =>
        (z : MTT.Qbar) ∈ K) ?_ ?_ ?_ ?_ haa
    · intro z hz
      obtain ⟨i, rfl⟩ := hz
      exact (IntermediateField.subset_adjoin ℚ T)
        (Set.mem_union_left _ ⟨i, rfl⟩)
    · exact K.zero_mem
    · intro x y _ _ hx hy
      exact K.add_mem hx hy
    · intro z x _ hx
      rw [show ((z • x : A) : MTT.Qbar) = z • (x : MTT.Qbar) from rfl,
        zsmul_eq_mul]
      exact K.mul_mem (K.intCast_mem z) hx
  have heps : ∀ a : ZMod N, f.epsilon a ∈ K := by
    intro a
    exact (IntermediateField.subset_adjoin ℚ T)
      (Set.mem_union_right _ ⟨a, rfl⟩)
  have hprime : ∀ q : ℕ, q.Prime → f.coeff q ∈ K := by
    intro q hq
    apply hAK
    intro x hx
    exact hstable q hq x hx
  have hperiod : (1 : ℝ) ∈ (MTT.GammaOne N).strictPeriods := by
    rw [show MTT.GammaOne N =
      (CongruenceSubgroup.Gamma1 N : Subgroup (GL (Fin 2) ℝ)) from rfl,
      CongruenceSubgroup.strictPeriods_Gamma1]
    exact ⟨1, by simp⟩
  letI : Fact (IsCusp OnePoint.infty (MTT.GammaOne N)) :=
    ⟨(MTT.GammaOne N).isCusp_of_mem_strictPeriods one_pos hperiod⟩
  have hzero : f.coeff 0 = 0 := by
    apply ι.injective
    rw [← f.coeff_eq 0]
    simpa using CuspFormClass.qExpansion_coeff_zero f.form one_pos hperiod
  have hcoeff : ∀ n : ℕ, f.coeff n ∈ K := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        rcases n with _ | n
        · simpa [hzero] using K.zero_mem
        · by_cases hn : n + 1 = 1
          · simpa [hn, f.normalized] using K.one_mem
          · obtain ⟨q, hq, hqdiv⟩ := Nat.exists_prime_and_dvd hn
            let m := (n + 1) / q
            have hnpos : 0 < n + 1 := Nat.succ_pos n
            have hm_lt : m < n + 1 := Nat.div_lt_self hnpos hq.one_lt
            have hqm : q * m = n + 1 := Nat.mul_div_cancel' hqdiv
            have hmdiv_lt : m / q < n + 1 :=
              lt_of_le_of_lt (Nat.div_le_self m q) hm_lt
            have hcorr : f.epsilon q * (q : MTT.Qbar) ^ (k - 1) *
                (if q ∣ m then f.coeff (m / q) else 0) ∈ K := by
              have hqK : (q : MTT.Qbar) ∈ K := by
                simpa using K.intCast_mem (q : ℤ)
              apply K.mul_mem (K.mul_mem (heps q) (K.pow_mem hqK _))
              split
              · exact ih (m / q) hmdiv_lt
              · exact K.zero_mem
            have hprod : f.coeff q * f.coeff m ∈ K :=
              K.mul_mem (hprime q hq) (ih m hm_lt)
            have hsub := K.sub_mem hprod hcorr
            have heq := MTT.Eigenform.hecke_recurrence hN ι f q hq m
            rw [← heq] at hsub
            rw [hqm] at hsub
            simpa using hsub
  have hle : f.coefficientField ≤ K := by
    apply Subfield.closure_le.2
    intro x hx
    rcases hx with hx | hx
    · obtain ⟨n, rfl⟩ := hx
      exact hcoeff n
    · obtain ⟨a, rfl⟩ := hx
      exact heps a
  let inc : f.coefficientField →ₗ[ℚ] K :=
    (Subfield.inclusion hle).toRatAlgHom.toLinearMap
  apply FiniteDimensional.of_injective inc
  intro x y hxy
  apply Subtype.ext
  simpa [inc, Subfield.inclusion] using congrArg Subtype.val hxy

end CoefficientFieldFinite
