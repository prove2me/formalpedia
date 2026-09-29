-- Prove2me | solution 1 for Gribov.reduced_gauge_group_homotopy_nontrivial
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-26T21:25:04.151003+00:00
-- url     : https://prove2.me/submissions/152b391c-2115-474a-9ed0-b4732ef508d7

import Mathlib
import Definitions.Def_gribov_gauge_group

/-! 8d72f4dc Gribov.reduced_gauge_group_homotopy_nontrivial (Singer 1978, Theorem 3 as formalised).

Route (j = 0, works for every r and every N >= 2). The formal reduced gauge group is
`C(S^r, SU N) ⧸ Z_N` with `Z_N` the finite subgroup of constant central maps, so the quotient map
`q` is a covering map. The path of constant maps from `1` to `const (ω • 1)` (`ω = exp(2πi/N)`)
projects to a loop `L` at `1` in the reduced gauge group. If `L` were null-homotopic, homotopy
lifting through `q` would force the lift of `L` from `1` (which is the path itself, ending at
`const (ω • 1)`) and the lift of the constant loop (ending at `1`) to have the same endpoint, so
`const (ω • 1) = 1`, contradicting `ω ≠ 1`. Hence `π_1` is nontrivial. -/

set_option autoImplicit false

open scoped Topology

namespace GribovLib
open Gribov
open scoped Topology

instance instIsTopologicalGroupGaugeGroup (r N : ℕ) : IsTopologicalGroup C(Sphere r, SU N) where
  continuous_inv :=
    ContinuousMap.continuous_postcomp (X := Sphere r)
      (⟨fun x : SU N => x⁻¹, continuous_inv⟩ : C(SU N, SU N))

theorem pi1_nontrivial_core (r N : ℕ)
    (hdisc : IsDiscrete ((CentralConstants (Sphere r) N : Subgroup _) : Set (GaugeGroup (Sphere r) N)))
    (c : GaugeGroup (Sphere r) N) (hc : c ∈ CentralConstants (Sphere r) N) (hc1 : c ≠ 1)
    (γ : Path (1 : GaugeGroup (Sphere r) N) c) :
    Nontrivial (FundamentalGroup (ReducedGaugeGroup (Sphere r) N) 1) := by
  set G := ReducedGaugeGroup (Sphere r) N
  let q : GaugeGroup (Sphere r) N → G := QuotientGroup.mk
  have cov : IsCoveringMap q := (Subgroup.isQuotientCoveringMap _ hdisc).isCoveringMap
  have hqc : q c = 1 := by
    apply (QuotientGroup.eq_one_iff c).mpr hc
  have hq_cont : Continuous q := continuous_quotient_mk'
  let L : Path (1 : G) 1 :=
    { toFun := fun t => q (γ t)
      continuous_toFun := hq_cont.comp γ.continuous
      source' := by simp [q]
      target' := by simp [hqc] }
  refine ⟨⟨FundamentalGroup.fromPath (Quotient.mk _ L),
    FundamentalGroup.fromPath (Quotient.mk _ (Path.refl _)), ?_⟩⟩
  intro hL
  obtain ⟨F⟩ := (Quotient.exact hL : Path.Homotopic L (Path.refl _))
  let Γ : C(unitInterval, G) := L.toContinuousMap
  have h0 : Γ 0 = q 1 := by simp [Γ, q]
  have h0' : (Path.refl (1 : G)).toContinuousMap 0 = q 1 := by simp [q]
  have hrefl : (Path.refl (1 : G)).toContinuousMap = ContinuousMap.const _ (q 1) := by
    ext t; simp [q]
  have := cov.liftPath_apply_one_eq_of_homotopicRel ⟨F⟩ 1 h0 h0'
  have hlift : cov.liftPath Γ 1 h0 = ⟨γ, γ.continuous⟩ :=
    ((cov.eq_liftPath_iff' h0).mpr ⟨rfl, γ.source⟩).symm
  have hlift' : cov.liftPath (Path.refl (1 : G)).toContinuousMap 1 h0' =
      ContinuousMap.const _ (1 : GaugeGroup (Sphere r) N) := by
    symm
    refine (cov.eq_liftPath_iff' h0').mpr ⟨?_, rfl⟩
    funext t; simp [q]
  rw [hlift, hlift'] at this
  exact hc1 (by simpa using this)
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

open Gribov Topology in
theorem solution (r N : ℕ) (hr : r = 3 ∨ r = 4)
    (hN : 2 ≤ N) :
    ∃ j : ℕ, Nontrivial (π_ (j + 1) (ReducedGaugeGroup (Sphere r) N) 1) := by
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
  have := GribovLib.pi1_nontrivial_core r N hdisc c hc hc1 γ
  exact ⟨0, (HomotopyGroup.pi1EquivFundamentalGroup).nontrivial⟩
