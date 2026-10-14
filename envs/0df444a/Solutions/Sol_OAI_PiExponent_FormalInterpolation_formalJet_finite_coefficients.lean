-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.formalJet_finite_coefficients
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-12T18:24:58.639249+00:00
-- url     : https://prove2.me/submissions/a464a9f6-b53d-41c3-994a-bb63a1b0ea1f

import Definitions.Def_OAI_PiExponent_FormalInterpolationPackets
import Mathlib.RingTheory.MvPowerSeries.Substitution

open OAI.PiExponent

noncomputable section

lemma liftSeries_eq_toMvPowerSeries (m : ℕ) (f : PowerSeries ℂ) :
    FormalInterpolation.liftSeries m f = f.toMvPowerSeries (0 : Fin (m + 1)) := by
  classical
  apply (MvPowerSeries.finSuccEquiv ℂ m).injective
  ext n x
  change MvPowerSeries.coeff x (PowerSeries.coeff n
    ((MvPowerSeries.finSuccEquiv ℂ m)
      ((MvPowerSeries.finSuccEquiv ℂ m).symm (PowerSeries.map MvPowerSeries.C f)))) = _
  rw [AlgEquiv.apply_symm_apply,
    PowerSeries.coeff_map, MvPowerSeries.coeff_coeff_finSuccEquiv]
  by_cases hx : x = 0
  · subst x
    have hd : Finsupp.embDomain (Function.Embedding.punit (0 : Fin (m + 1)))
        (Finsupp.single () n) = (0 : Fin m →₀ ℕ).cons n := by
      ext i
      refine Fin.cases ?_ (fun j => ?_) i <;> simp [Function.Embedding.punit]
    rw [← hd]
    simpa [PowerSeries.toMvPowerSeries, PowerSeries.toMvPowerSeries_apply, Function.Embedding.punit] using
      (MvPowerSeries.coeff_embDomain_rename
        (Function.Embedding.punit (0 : Fin (m + 1))) f (Finsupp.single () n)).symm
  · rw [MvPowerSeries.coeff_C, if_neg hx]
    symm
    apply MvPowerSeries.coeff_rename_eq_zero
    rintro ⟨d, hd⟩
    obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
      by_contra! h
      exact hx (Finsupp.ext h)
    rw [Finsupp.unique_single d] at hd
    have h := congrArg (fun z : Fin (m + 1) →₀ ℕ => z i.succ) hd
    exact hi (by simpa [Finsupp.single_apply] using h.symm)

theorem solution
    {m : Nat} (c : Fin m -> Complex)
    (S : Finset (Fin (m + 1) -> Nat))
    (Q : MvPolynomial (Fin (m + 1)) Complex) :
    Exists fun P : MvPolynomial (Fin (m + 1)) Complex =>
      forall a, Membership.mem S a ->
        MvPowerSeries.coeff (InterpolationMatrix.exponentVector a)
          (FormalInterpolation.formalJet c P) =
        MvPowerSeries.coeff (InterpolationMatrix.exponentVector a)
          (Q : MvPowerSeries (Fin (m + 1)) Complex) := by
  classical
  let L : MvPowerSeries (Fin (m + 1)) ℂ :=
    FormalInterpolation.liftSeries m (PowerSeries.log ℂ)
  let v : Fin (m + 1) → MvPowerSeries (Fin (m + 1)) ℂ :=
    Fin.cases (MvPowerSeries.X 0) (fun i => MvPowerSeries.X i.succ + L)
  have hL : MvPowerSeries.constantCoeff L = 0 := by
    simp [L, liftSeries_eq_toMvPowerSeries, PowerSeries.toMvPowerSeries_apply,
      MvPowerSeries.constantCoeff_rename, ← PowerSeries.constantCoeff_eq]
  have hv : ∀ i, MvPowerSeries.constantCoeff (v i) = 0 := by
    intro i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp [v, hL]
  have hs : MvPowerSeries.HasSubst v :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero hv
  let F := MvPowerSeries.substAlgHom (R := ℂ) hs
  have hfix : F L = L := by
    change MvPowerSeries.substAlgHom hs L = L
    rw [MvPowerSeries.substAlgHom_apply]
    rw [show L = (PowerSeries.log ℂ).toMvPowerSeries (0 : Fin (m + 1)) from
      liftSeries_eq_toMvPowerSeries m _]
    rw [PowerSeries.subst_toMvPowerSeries hs]
    simp only [v, Fin.cases_zero]
    exact PowerSeries.toMvPowerSeries_eq_subst.symm
  let b : Fin (m + 1) → MvPowerSeries (Fin (m + 1)) ℂ :=
    Fin.cases (MvPowerSeries.X 0) (fun i => MvPowerSeries.X i.succ - L)
  have hFb : ∀ i, F (b i) = MvPowerSeries.X i := by
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · change MvPowerSeries.substAlgHom hs (MvPowerSeries.X 0) = _
      rw [MvPowerSeries.substAlgHom_X]
      rfl
    · simp only [b, Fin.cases_succ, map_sub, hfix]
      rw [show F (MvPowerSeries.X j.succ) = v j.succ from
        MvPowerSeries.substAlgHom_X hs j.succ]
      simp [v]
  have hcomp : F.comp (MvPolynomial.aeval b) =
      MvPolynomial.aeval (MvPowerSeries.X : Fin (m + 1) → MvPowerSeries (Fin (m + 1)) ℂ) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp [AlgHom.comp_apply, hFb]
  have hcoe (R : MvPolynomial (Fin (m + 1)) ℂ) :
      MvPolynomial.aeval MvPowerSeries.X R = (R : MvPowerSeries (Fin (m + 1)) ℂ) := by
    rw [← MvPowerSeries.subst_coe, MvPowerSeries.subst_self]
    rfl
  let f := MvPolynomial.aeval b Q
  have hinv : MvPowerSeries.subst v f = (Q : MvPowerSeries (Fin (m + 1)) ℂ) := by
    rw [← MvPowerSeries.substAlgHom_apply hs]
    change (F.comp (MvPolynomial.aeval b)) Q = _
    rw [hcomp, hcoe]
  let t : Fin (m + 1) → MvPolynomial (Fin (m + 1)) ℂ :=
    Fin.cases (MvPolynomial.X 0 - 1)
      (fun i => MvPolynomial.X i.succ - MvPolynomial.C (c i))
  let tr : MvPolynomial (Fin (m + 1)) ℂ →ₐ[ℂ] MvPolynomial (Fin (m + 1)) ℂ :=
    MvPolynomial.aeval t
  have htrans : (FormalInterpolation.formalJet c).comp tr = MvPolynomial.aeval v := by
    apply MvPolynomial.algHom_ext
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [tr, t, FormalInterpolation.formalJet, v]
    · simp [tr, t, FormalInterpolation.formalJet, v, L, MvPowerSeries.algebraMap_apply,
        add_assoc]
  have htr (R : MvPolynomial (Fin (m + 1)) ℂ) :
      FormalInterpolation.formalJet c (tr R) =
        MvPowerSeries.subst v (R : MvPowerSeries (Fin (m + 1)) ℂ) := by
    change ((FormalInterpolation.formalJet c).comp tr) R = _
    rw [htrans, MvPowerSeries.subst_coe]
  let k := S.sup (fun a => (InterpolationMatrix.exponentVector a).degree) + 1
  refine ⟨tr (f.truncTotal k), ?_⟩
  intro a ha
  have hd : (InterpolationMatrix.exponentVector a).degree < k :=
    Nat.lt_succ_of_le (Finset.le_sup
      (f := fun a => (InterpolationMatrix.exponentVector a).degree) ha)
  have ht := MvPowerSeries.truncTotal_subst_eq_truncTotal_truncTotal_subst
    (f := f) (k := k) hv
  rw [hinv] at ht
  have hc := congrArg (MvPolynomial.coeff (InterpolationMatrix.exponentVector a)) ht
  rw [MvPowerSeries.coeff_truncTotal _ hd, MvPowerSeries.coeff_truncTotal _ hd] at hc
  rw [htr]
  exact hc.symm
