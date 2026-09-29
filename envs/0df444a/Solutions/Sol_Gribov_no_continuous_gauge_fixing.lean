-- Prove2me | solution 1 for Gribov.no_continuous_gauge_fixing
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-24T17:53:14.757349+00:00
-- url     : https://prove2.me/submissions/9e5d1c3d-bb95-4618-a6e0-c3c96b1913a4

import Mathlib
import Definitions.Def_gribov_gauge_group
import Definitions.Def_gribov_gauge_fixing

/-! 08172c4e Gribov.no_continuous_gauge_fixing (Singer 1978, Corollary 4 as formalised).

Route. The formal reduced gauge group is `C(S^r, SU N) ⧸ Z_N` with `Z_N` the (finite) subgroup of
constant central maps, so the quotient map `q` is a covering map. A continuous section `s` of
`A → A / G` plus the continuous division map `d` makes `G` a retract of the weakly contractible
space `A`. The path of constant maps from `1` to `const (ω • 1)` (`ω = exp(2πi/N)`) projects to a
loop in `G`; that loop is null in `A`, hence null in `G`, and homotopy lifting through `q` forces
`const (ω • 1) = 1`, contradicting `ω ≠ 1` for `N ≥ 2`. -/

set_option autoImplicit false

namespace GribovLib
open Gribov
open scoped Topology

instance instIsTopologicalGroupGaugeGroup (r N : ℕ) : IsTopologicalGroup C(Sphere r, SU N) where
  continuous_inv :=
    ContinuousMap.continuous_postcomp (X := Sphere r)
      (⟨fun x : SU N => x⁻¹, continuous_inv⟩ : C(SU N, SU N))

theorem core (r N : ℕ) (A : Type) [TopologicalSpace A]
    [MulAction (ReducedGaugeGroup (Sphere r) N) A]
    [ContinuousSMul (ReducedGaugeGroup (Sphere r) N) A]
    (hprin : IsPrincipalAction (ReducedGaugeGroup (Sphere r) N) A)
    (hwc : IsWeaklyContractible A)
    (hdisc : IsDiscrete ((CentralConstants (Sphere r) N : Subgroup _) : Set (GaugeGroup (Sphere r) N)))
    (c : GaugeGroup (Sphere r) N) (hc : c ∈ CentralConstants (Sphere r) N) (hc1 : c ≠ 1)
    (γ : Path (1 : GaugeGroup (Sphere r) N) c) :
    ¬ ∃ s : OrbitSpace (ReducedGaugeGroup (Sphere r) N) A → A,
        IsGaugeFixing (ReducedGaugeGroup (Sphere r) N) A s := by
  rintro ⟨s, hs_cont, hs_sec⟩
  obtain ⟨hfree, d, hd_cont, hd⟩ := hprin
  obtain ⟨⟨a0⟩, hpi⟩ := hwc
  set G := ReducedGaugeGroup (Sphere r) N
  set x0 := s (Quotient.mk _ a0) with hx0
  have hmem : ∀ a : A, ∃ g : G, g • s (Quotient.mk _ a) = a := by
    intro a
    have h : s (Quotient.mk _ a) ∈ MulAction.orbit G a :=
      MulAction.orbitRel_apply.mp (Quotient.exact (hs_sec (Quotient.mk _ a)))
    obtain ⟨g, hg⟩ := h
    exact ⟨g⁻¹, by rw [← hg, inv_smul_smul]⟩
  let ret : A → G := fun a => d ⟨(a, s (Quotient.mk _ a)), hmem a⟩
  have hret : Continuous ret :=
    hd_cont.comp (Continuous.subtype_mk
      (continuous_id.prodMk (hs_cont.comp continuous_quotient_mk')) _)
  have hsx : ∀ g : G, s (Quotient.mk _ (g • x0)) = x0 := by
    intro g
    have h1 : (Quotient.mk (MulAction.orbitRel G A) (g • x0)) = Quotient.mk _ a0 := by
      rw [Quotient.sound ((MulAction.orbitRel_apply).mpr (MulAction.mem_orbit x0 g))]
      exact hs_sec _
    rw [h1]
  have hri : ∀ g : G, ret (g • x0) = g := by
    intro g
    have key : ∀ p : {p : A × A // ∃ g : G, g • p.2 = p.1},
        p.1.1 = g • x0 → p.1.2 = x0 → d p = g := by
      intro p h1 h2
      have h := hd p
      rw [h1, h2] at h
      have h3 : (g⁻¹ * d p) • x0 = x0 := by rw [mul_smul, h, inv_smul_smul]
      exact (inv_mul_eq_one.mp (hfree _ _ h3)).symm
    exact key _ rfl (hsx g)
  let q : GaugeGroup (Sphere r) N → G := QuotientGroup.mk
  have cov : IsCoveringMap q := (Subgroup.isQuotientCoveringMap _ hdisc).isCoveringMap
  have hqc : q c = q 1 := by
    apply (QuotientGroup.eq).mpr
    simpa using inv_mem hc
  have hq_cont : Continuous q := continuous_quotient_mk'
  let Γ : C(unitInterval, G) := ⟨fun t => q (γ t), hq_cont.comp γ.continuous⟩
  let L : Path ((q 1) • x0) ((q 1) • x0) :=
    { toFun := fun t => (q (γ t)) • x0
      continuous_toFun := (hq_cont.comp γ.continuous).smul continuous_const
      source' := by simp
      target' := by simp [hqc] }
  have hL : Path.Homotopic L (Path.refl _) := by
    have := hpi 1 ((q 1) • x0)
    have hsub : Subsingleton (FundamentalGroup A ((q 1) • x0)) :=
      (HomotopyGroup.pi1EquivFundamentalGroup).symm.subsingleton
    exact Quotient.exact (Subsingleton.elim (α := FundamentalGroup A ((q 1) • x0))
      (FundamentalGroup.fromPath (Quotient.mk _ L))
      (FundamentalGroup.fromPath (Quotient.mk _ (Path.refl _))))
  obtain ⟨F⟩ := hL
  let retC : C(A, G) := ⟨ret, hret⟩
  have F' := F.compContinuousMap retC
  have e1 : retC.comp L.toContinuousMap = Γ := by
    ext t; exact hri _
  have e2 : retC.comp (Path.refl ((q 1) • x0)).toContinuousMap = ContinuousMap.const _ (q 1) := by
    ext t; exact hri _
  rw [e1, e2] at F'
  have h0 : Γ 0 = q 1 := by simp [Γ]
  have := cov.liftPath_apply_one_eq_of_homotopicRel ⟨F'⟩ 1 h0 rfl
  have h2 := congrArg (fun f : C(unitInterval, GaugeGroup (Sphere r) N) => f 1)
    (cov.liftPath_const (e := (1 : GaugeGroup (Sphere r) N)) (x := q 1) rfl)
  have hlift : cov.liftPath Γ 1 h0 = ⟨γ, γ.continuous⟩ :=
    ((cov.eq_liftPath_iff' h0).mpr ⟨rfl, γ.source⟩).symm
  have h4 := this.trans h2
  rw [hlift] at h4
  exact hc1 (by simpa using h4)
end GribovLib

namespace GribovLib
open Gribov
open Matrix

theorem center_offdiag (N : ℕ) (c : SU N) (hc : c ∈ Subgroup.center (SU N))
    (i j : Fin N) (hij : i ≠ j) : (c : Matrix (Fin N) (Fin N) ℂ) i j = 0 := by
  let d : Fin N → ℂ := fun k =>
    (Pi.mulSingle i Complex.I : Fin N → ℂ) k * (Pi.mulSingle j (-Complex.I) : Fin N → ℂ) k
  have hD : Matrix.diagonal d ∈ Matrix.specialUnitaryGroup (Fin N) ℂ := by
    rw [Matrix.mem_specialUnitaryGroup_iff, Matrix.mem_unitaryGroup_iff]
    constructor
    · rw [Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose,
        Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
      congr 1; funext k
      by_cases hki : k = i
      · subst hki; simp [d, Pi.mulSingle_apply, hij]
      · by_cases hkj : k = j
        · subst hkj; simp [d, Pi.mulSingle_apply, hki]
        · simp [d, Pi.mulSingle_apply, hki, hkj]
    · rw [Matrix.det_diagonal, Finset.prod_mul_distrib, Finset.prod_pi_mulSingle',
        Finset.prod_pi_mulSingle']
      simp
  have hcomm := Subgroup.mem_center_iff.mp hc ⟨_, hD⟩
  have h := congrArg (fun M : SU N => (M : Matrix (Fin N) (Fin N) ℂ) i j) hcomm
  simp only [MulMemClass.coe_mul] at h
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul] at h
  simp [d, Pi.mulSingle_apply, hij, Ne.symm hij] at h
  have h2 : (2 * Complex.I) * (c : Matrix (Fin N) (Fin N) ℂ) i j = 0 := by linear_combination h
  exact (mul_eq_zero.mp h2).resolve_left (by simp)

theorem center_diag_eq (N : ℕ) (c : SU N) (hc : c ∈ Subgroup.center (SU N))
    (i j : Fin N) (hij : i ≠ j) :
    (c : Matrix (Fin N) (Fin N) ℂ) i i = (c : Matrix (Fin N) (Fin N) ℂ) j j := by
  let R : Matrix (Fin N) (Fin N) ℂ :=
    (Equiv.swap i j).permMatrix ℂ * Matrix.diagonal (Pi.mulSingle i (-1 : ℂ) : Fin N → ℂ)
  have hR : R ∈ Matrix.specialUnitaryGroup (Fin N) ℂ := by
    rw [Matrix.mem_specialUnitaryGroup_iff, Matrix.mem_unitaryGroup_iff]
    constructor
    · simp only [R, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_mul,
        Matrix.diagonal_conjTranspose, Matrix.conjTranspose_permMatrix]
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc (Matrix.diagonal _), Matrix.diagonal_mul_diagonal]
      have : (fun k => (Pi.mulSingle i (-1 : ℂ) : Fin N → ℂ) k * star (Pi.mulSingle i (-1 : ℂ) : Fin N → ℂ) k) = 1 := by
        funext k; by_cases hk : k = i
        · subst hk; simp
        · simp [hk]
      rw [this, show (Matrix.diagonal (1 : Fin N → ℂ)) = 1 from Matrix.diagonal_one, Matrix.one_mul]
      rw [← Matrix.permMatrix_mul, inv_mul_cancel, Matrix.permMatrix_one]
    · simp [R, Matrix.det_mul, Matrix.det_permutation, Equiv.Perm.sign_swap hij,
        Matrix.det_diagonal, Finset.prod_pi_mulSingle']
  have hcd : (c : Matrix (Fin N) (Fin N) ℂ) =
      Matrix.diagonal (fun k => (c : Matrix (Fin N) (Fin N) ℂ) k k) := by
    ext a b
    by_cases hab : a = b
    · subst hab; simp
    · rw [Matrix.diagonal_apply_ne _ hab]; exact center_offdiag N c hc a b hab
  have hcomm := Subgroup.mem_center_iff.mp hc ⟨_, hR⟩
  have h := congrArg (fun M : SU N => (M : Matrix (Fin N) (Fin N) ℂ) i j) hcomm
  simp only [MulMemClass.coe_mul] at h
  rw [hcd, Matrix.mul_diagonal, Matrix.diagonal_mul] at h
  have hRij : R i j = 1 := by
    simp [R, Matrix.mul_diagonal, Ne.symm hij, Equiv.Perm.permMatrix,
      PEquiv.toMatrix_apply, Equiv.swap_apply_left]
  rw [hRij] at h
  simpa using h.symm
end GribovLib

namespace GribovLib
open Gribov
open Matrix

theorem center_eq_diag (N : ℕ) (hN : 0 < N) (c : SU N) (hc : c ∈ Subgroup.center (SU N)) :
    (c : Matrix (Fin N) (Fin N) ℂ) =
      Matrix.diagonal (fun _ => (c : Matrix (Fin N) (Fin N) ℂ) ⟨0, hN⟩ ⟨0, hN⟩) := by
  ext a b
  by_cases hab : a = b
  · subst hab
    rw [Matrix.diagonal_apply_eq]
    by_cases ha : a = ⟨0, hN⟩
    · rw [ha]
    · exact center_diag_eq N c hc a _ ha
  · rw [Matrix.diagonal_apply_ne _ hab]; exact center_offdiag N c hc a b hab

theorem center_finite (N : ℕ) (hN : 0 < N) : (Subgroup.center (SU N) : Set (SU N)).Finite := by
  refine Set.Finite.of_finite_image
    (f := fun c : SU N => (c : Matrix (Fin N) (Fin N) ℂ) ⟨0, hN⟩ ⟨0, hN⟩) ?_ ?_
  · refine (Polynomial.nthRootsFinset N (1 : ℂ)).finite_toSet.subset ?_
    rintro _ ⟨c, hc, rfl⟩
    rw [Finset.mem_coe, Polynomial.mem_nthRootsFinset hN]
    have hdet := (Matrix.mem_specialUnitaryGroup_iff.mp c.2).2
    rw [center_eq_diag N hN c hc, Matrix.det_diagonal, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin] at hdet
    exact hdet
  · intro c hc d hd hcd
    apply Subtype.ext
    rw [center_eq_diag N hN c hc, center_eq_diag N hN d hd]
    simp only at hcd
    rw [hcd]

theorem centralConstants_finite (r N : ℕ) (hN : 0 < N) :
    ((CentralConstants (Sphere r) N : Subgroup _) : Set (GaugeGroup (Sphere r) N)).Finite := by
  refine ((center_finite N hN).image (fun c : SU N => ContinuousMap.const (Sphere r) c)).subset ?_
  intro φ hφ
  obtain ⟨c, hc, hφc⟩ := hφ
  exact ⟨c, hc, ContinuousMap.ext fun x => (hφc x).symm⟩

theorem exists_central_path (N : ℕ) (hN : 2 ≤ N) :
    ∃ z : SU N, z ∈ Subgroup.center (SU N) ∧ z ≠ 1 ∧ Joined (1 : SU N) z := by
  have hN0 : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  let i0 : Fin N := ⟨0, by omega⟩
  let θ : ℝ → Fin N → ℝ := fun t k => 2 * Real.pi * (t / N - if k = i0 then t else 0)
  let M : ℝ → Matrix (Fin N) (Fin N) ℂ := fun t =>
    Matrix.diagonal fun k => Complex.exp (↑(θ t k) * Complex.I)
  have hM : ∀ t, M t ∈ Matrix.specialUnitaryGroup (Fin N) ℂ := by
    intro t
    rw [Matrix.mem_specialUnitaryGroup_iff, Matrix.mem_unitaryGroup_iff]
    constructor
    · rw [Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose,
        Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
      congr 1; funext k
      rw [Pi.star_apply, Complex.star_def, Complex.mul_conj', Complex.norm_exp_ofReal_mul_I]
      simp
    · rw [Matrix.det_diagonal, ← Complex.exp_sum, ← Finset.sum_mul, ← Complex.ofReal_sum]
      have hs : ∑ k, θ t k = 0 := by
        simp only [θ, ← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_const,
          Finset.card_univ, Fintype.card_fin, Finset.sum_ite_eq', Finset.mem_univ, if_true,
          nsmul_eq_mul]
        field_simp
        ring
      rw [hs]; simp
  have hMc : Continuous M := by
    refine Continuous.matrix_diagonal (continuous_pi fun k => ?_)
    refine Complex.continuous_exp.comp ((Complex.continuous_ofReal.comp ?_).mul continuous_const)
    by_cases hk : k = i0
    · simp only [θ, hk, if_true]; fun_prop
    · simp only [θ, hk, if_false]; fun_prop
  let u : unitInterval → SU N := fun t => ⟨M t, hM t⟩
  have hu : Continuous u := Continuous.subtype_mk (hMc.comp continuous_subtype_val) _
  have hu0 : u 0 = 1 := by
    apply Subtype.ext
    simp [u, M, θ]
  have hz : (u 1 : Matrix (Fin N) (Fin N) ℂ) =
      Matrix.diagonal (fun _ => Complex.exp (2 * Real.pi * Complex.I / N)) := by
    show Matrix.diagonal (fun k => Complex.exp (↑(θ 1 k) * Complex.I)) = _
    congr 1; funext k
    by_cases hk : k = i0
    · simp only [θ, hk, if_true]
      rw [show (↑(2 * Real.pi * (1 / (N : ℝ) - 1)) * Complex.I : ℂ)
          = 2 * Real.pi * Complex.I / N - 2 * Real.pi * Complex.I by push_cast; ring,
        Complex.exp_sub, Complex.exp_two_pi_mul_I, div_one]
    · simp only [θ, hk, if_false]
      congr 1; push_cast; ring
  refine ⟨u 1, ?_, ?_, ⟨⟨⟨u, hu⟩, hu0, rfl⟩⟩⟩
  · rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    simp only [MulMemClass.coe_mul]
    rw [hz]
    ext i j
    simp [Matrix.mul_diagonal, Matrix.diagonal_mul, mul_comm]
  · intro h
    have h1 := congrArg (fun g : SU N => (g : Matrix (Fin N) (Fin N) ℂ) i0 i0) h
    simp only [hz, Matrix.diagonal_apply_eq, OneMemClass.coe_one, Matrix.one_apply_eq] at h1
    exact (Complex.isPrimitiveRoot_exp N (by omega)).ne_one (by omega) h1

end GribovLib

set_option maxHeartbeats 4000000 in
open Gribov in
theorem solution (r N : ℕ) (hr : r = 3 ∨ r = 4) (hN : 2 ≤ N)
    (A : Type) [TopologicalSpace A]
    [MulAction (ReducedGaugeGroup (Sphere r) N) A]
    [ContinuousSMul (ReducedGaugeGroup (Sphere r) N) A]
    (hprin : IsPrincipalAction (ReducedGaugeGroup (Sphere r) N) A)
    (hwc : IsWeaklyContractible A) :
    ¬ ∃ s : OrbitSpace (ReducedGaugeGroup (Sphere r) N) A → A,
        IsGaugeFixing (ReducedGaugeGroup (Sphere r) N) A s := by
  obtain ⟨z, hz, hz1, ⟨p⟩⟩ := GribovLib.exists_central_path N hN
  have hdisc := (GribovLib.centralConstants_finite r N (by omega)).isDiscrete
  let c : GaugeGroup (Sphere r) N := ContinuousMap.const _ z
  have hc : c ∈ CentralConstants (Sphere r) N := ⟨z, hz, fun _ => rfl⟩
  have hc1 : c ≠ 1 := fun h =>
    hz1 (congrArg (fun φ : GaugeGroup (Sphere r) N => φ (northPole r)) h)
  let γ : Path (1 : GaugeGroup (Sphere r) N) c :=
    { toFun := fun t => ContinuousMap.const _ (p t)
      continuous_toFun := ContinuousMap.continuous_const'.comp p.continuous
      source' := ContinuousMap.ext fun x => by simp
      target' := ContinuousMap.ext fun x => by simp [c] }
  exact GribovLib.core r N A hprin hwc hdisc c hc hc1 γ
