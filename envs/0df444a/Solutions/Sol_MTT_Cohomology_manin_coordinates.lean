-- Prove2me | solution 1 for MTT.Cohomology.manin_coordinates
-- status  : ACCEPTED   (prove)
-- author  : @allychan327
-- created : 2026-09-06T17:16:15.855103+00:00
-- url     : https://prove2.me/submissions/1cf49961-4b60-495a-b1bf-70eccb9a5b2d

import Definitions.Def_MTT_Cohomology
import Theorems.Thm_MTT_Cohomology_manin_generation

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
open scoped BigOperators
open MTT.Cohomology

namespace P2MMC

open MvPolynomial

variable {N n : ℕ} {R : Type*} [CommRing R]

theorem hc_hom (φ : Hc N n R) (x y : Cusp) : φ.val (x, y) ∈ MTT.Cohomology.Sym R n := φ.2.1 x y

theorem hc_equiv (φ : Hc N n R) (γ : CongruenceSubgroup.Gamma1 N) (x y : Cusp) :
    φ.val (cuspAct γ.val x, cuspAct γ.val y) = act γ.val.val (φ.val (x, y)) := φ.2.2.2 γ x y

theorem cuspAct_mul (g h : Matrix.SpecialLinearGroup (Fin 2) ℤ) (x : Cusp) :
    cuspAct (g * h) x = cuspAct g (cuspAct h x) := by
  simp [cuspAct, map_mul, mul_smul]

/-- The right-coset space of `Γ₁(N)` in `SL(2,ℤ)`. -/
abbrev Cos (N : ℕ) := Quotient (QuotientGroup.rightRel (CongruenceSubgroup.Gamma1 N))

instance cosFinite (N : ℕ) [NeZero N] : Finite (Cos N) :=
  Finite.of_equiv _
    (QuotientGroup.quotientRightRelEquivQuotientLeftRel (CongruenceSubgroup.Gamma1 N)).symm

/-- The finite index set of Manin coordinates. -/
abbrev Idx (N n : ℕ) := Cos N × Fin (n + 1)

/-- Reduction to coset representatives. -/
theorem hc_eq_zero_of_reps (φ : Hc N n R)
    (hR : ∀ q : Cos N,
      φ.val (cuspAct q.out ((0 : ℚ) : Cusp), cuspAct q.out OnePoint.infty) = 0) :
    φ = 0 := by
  refine MTT.Cohomology.manin_generation φ fun g => ?_
  set q : Cos N := Quotient.mk _ g with hqdef
  have hmk : (Quotient.mk (QuotientGroup.rightRel (CongruenceSubgroup.Gamma1 N)) q.out)
      = Quotient.mk _ g := by rw [Quotient.out_eq]
  have hrel : g * (Quotient.out q)⁻¹ ∈ CongruenceSubgroup.Gamma1 N :=
    QuotientGroup.rightRel_apply.mp (Quotient.exact hmk)
  obtain ⟨γ, hγ⟩ : ∃ γ : CongruenceSubgroup.Gamma1 N, g = γ.val * q.out :=
    ⟨⟨g * (q.out)⁻¹, hrel⟩, by simp⟩
  rw [hγ, cuspAct_mul, cuspAct_mul, hc_equiv φ γ, hR q, map_zero]

/-- The exponent vector of `X^j Y^{n-j}`. -/
def mono (n j : ℕ) : Fin 2 →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun i : Fin 2 => if i = 0 then j else n - j)

theorem mono_apply (n j : ℕ) (i : Fin 2) : mono n j i = if i = 0 then j else n - j := rfl

theorem hom_eq_zero (P : Binary R) (hP : P ∈ MTT.Cohomology.Sym R n)
    (h : ∀ j : Fin (n + 1), MvPolynomial.coeff (mono n j.val) P = 0) : P = 0 := by
  rw [MvPolynomial.mem_homogeneousSubmodule] at hP
  ext d
  rw [MvPolynomial.coeff_zero]
  by_cases hdeg : d.degree = n
  · have hsum : d 0 + d 1 = n := by
      have hds := Finsupp.degree_eq_sum d
      rw [Fin.sum_univ_two] at hds
      rw [hds] at hdeg
      exact hdeg
    have hd : d = mono n (d 0) := by
      refine Finsupp.ext fun i => ?_
      fin_cases i
      · simp [mono_apply]
      · simp only [mono_apply]
        norm_num
        omega
    have := h ⟨d 0, by omega⟩
    rwa [← hd] at this
  · exact hP.coeff_eq_zero hdeg

variable [NeZero N]

/-- Manin coordinates: the `X^j Y^{n-j}` coefficients on the unimodular paths attached to a
fixed set of coset representatives. -/
def Coord (N n : ℕ) [NeZero N] (R : Type*) [CommRing R] :
    Hc N n R →ₗ[R] (Idx N n → R) where
  toFun φ z := MvPolynomial.coeff (mono n z.2.val)
      (φ.val (cuspAct z.1.out ((0 : ℚ) : Cusp), cuspAct z.1.out OnePoint.infty))
  map_add' φ ψ := by funext z; simp
  map_smul' c φ := by
    funext z
    show MvPolynomial.coeff _ ((c • φ).val _) = c * MvPolynomial.coeff _ (φ.val _)
    exact MvPolynomial.coeff_smul _ _ _

@[simp] theorem Coord_apply (φ : Hc N n R) (z : Idx N n) :
    Coord N n R φ z = MvPolynomial.coeff (mono n z.2.val)
      (φ.val (cuspAct z.1.out ((0 : ℚ) : Cusp), cuspAct z.1.out OnePoint.infty)) := rfl

theorem Coord_injective : Function.Injective (Coord N n R) := by
  rw [injective_iff_map_eq_zero]
  intro φ hφ
  refine hc_eq_zero_of_reps φ fun q => ?_
  refine hom_eq_zero _ (hc_hom φ _ _) fun j => ?_
  simpa using congrFun hφ (q, j)

end P2MMC

open P2MMC in
theorem solution {N n : ℕ} (hN : 0 < N) (R : Type*) [CommRing R] :
    ∃ (m : ℕ) (T : Hc N n R →ₗ[R] (Fin m → R)), Function.Injective T := by
  have : NeZero N := ⟨hN.ne'⟩
  have : Fintype (Idx N n) := Fintype.ofFinite _
  classical
  let e : Idx N n ≃ Fin (Fintype.card (Idx N n)) := Fintype.equivFin _
  refine ⟨Fintype.card (Idx N n),
    { toFun := fun φ i => Coord N n R φ (e.symm i)
      map_add' := fun φ ψ => by funext i; simp
      map_smul' := fun c φ => by funext i; simp }, ?_⟩
  intro φ ψ h
  refine Coord_injective (funext fun z => ?_)
  simpa using congrFun h (e z)
