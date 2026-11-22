-- Prove2me | solution 1 for NoHair.TwoCentre.not_israel_conclusion
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-22T21:23:18.927329+00:00
-- url     : https://prove2.me/submissions/c93a67b7-2987-42a1-9f97-a2cb35a60b65

import Definitions.Def_NoHair_TwoCentre
import Definitions.Def_NoHair_KerrNewmanEinstein_Atoms
import Definitions.Def_NoHair_KerrNewmanEinstein_MaxwellF

/-! The Kerr–Schild derivative and index-raising calculations below are from the accepted
Prove2Me solution f8c62ec4-e576-4bf9-aa5b-a5897df2f835 (Apache 2.0). -/

open NoHair NoHair.KNE
open scoped BigOperators

private lemma rnField (e : ℝ) (y : E4) (hy : 0 < ksRadius 0 y) (i j : Fin 4) :
    kerrNewmanField 0 e y i j =
      FA 0 e (ksRadius 0 y) (ksNull 0 y 1) (ksNull 0 y 2) (ksNull 0 y 3) (Wf 0 y) i j := by
  have hA : ∀ k, HasCP (fun z => kerrNewmanPotential 0 e z k) y
      (fun l => dHA 0 e (ksRadius 0 y) (ksNull 0 y 1) (ksNull 0 y 2) (ksNull 0 y 3)
          (Wf 0 y) l * ksNull 0 y k
        + e * ksRadius 0 y ^ 3 / (ksRadius 0 y ^ 4 + (0 : ℝ) ^ 2 * y 3 ^ 2)
          * dKt 0 (ksRadius 0 y) (ksNull 0 y 1) (ksNull 0 y 2) (ksNull 0 y 3)
            (Wf 0 y) k l) :=
    fun k => (hasCP_H 0 e y hy).mul (hasCP_K 0 y hy k)
  have hpot : e * ksRadius 0 y ^ 3 / (ksRadius 0 y ^ 4 + (0 : ℝ) ^ 2 * y 3 ^ 2) =
      HA 0 e (ksRadius 0 y) (Wf 0 y) := by
    simp [HA, Wf]
    field_simp [hy.ne']
  unfold kerrNewmanField
  rw [(hA j).eq i, (hA i).eq j, hpot,
    ← fS 0 e _ _ _ _ _ (ks_rel 0 y hy) (ks_W 0 y hy) i j]
  simp only [FS, Kv, ← ksNull_eq_Kv 0 y]

private lemma rnRaisedField (m e : ℝ) (y : E4) (hy : 0 < ksRadius 0 y) (i j : Fin 4) :
    raiseBoth (kerrNewmanMetric m 0 e) (kerrNewmanField 0 e) y i j =
      FupA 0 m e (ksRadius 0 y) (ksNull 0 y 1) (ksNull 0 y 2) (ksNull 0 y 3)
        (Wf 0 y) i j := by
  unfold raiseBoth
  simp only [invMetric_eq m 0 e y hy, Matrix.of_apply, rnField e y hy]
  exact fU 0 m e _ _ _ _ _ (ks_rel 0 y hy) (ks_W 0 y hy) i j

private lemma leviCivita_perm (p : Equiv.Perm (Fin 4)) :
    leviCivita (p 0) (p 1) (p 2) (p 3) = ((Equiv.Perm.sign p : ℤ) : ℝ) := by
  have hf : ![p 0, p 1, p 2, p 3] = (p : Fin 4 → Fin 4) := by
    funext i
    fin_cases i <;> rfl
  have hp : Equiv.ofBijective (p : Fin 4 → Fin 4) p.bijective = p := by
    ext i
    rfl
  simp [leviCivita, hf, hp]

private theorem epsilon_repeat (a b c d s t : Fin 4) (hne : s ≠ t)
    (h : (![a,b,c,d] : Fin 4 → Fin 4) s = ![a,b,c,d] t) : leviCivita a b c d = 0 := by
  unfold leviCivita
  exact dif_neg (fun hbij => hne (hbij.1 h))

private theorem epsAC (a b c : Fin 4) : leviCivita a b a c = 0 :=
  epsilon_repeat a b a c 0 2 (by decide) rfl
private theorem epsAD (a b c : Fin 4) : leviCivita a b c a = 0 :=
  epsilon_repeat a b c a 0 3 (by decide) rfl
private theorem epsBC (a b c : Fin 4) : leviCivita a b b c = 0 :=
  epsilon_repeat a b b c 1 2 (by decide) rfl
private theorem epsBD (a b c : Fin 4) : leviCivita a b c b = 0 :=
  epsilon_repeat a b c b 1 3 (by decide) rfl

private lemma oriented_eps (p : Equiv.Perm (Fin 4)) (hp : Equiv.Perm.sign p = 1) :
    leviCivita (p 0) (p 1) (p 2) (p 3) = 1 ∧ leviCivita (p 0) (p 1) (p 3) (p 2) = -1 := by
  constructor
  · simp [leviCivita_perm, hp]
  · let q := p * Equiv.swap (2 : Fin 4) 3
    have h := leviCivita_perm q
    have h0 : Equiv.swap (2 : Fin 4) 3 0 = 0 := by decide
    have h1 : Equiv.swap (2 : Fin 4) 3 1 = 1 := by decide
    simpa [q, hp, Equiv.Perm.mul_apply, h0, h1] using h

private lemma pair_forces_zero (β x : ℝ)
    (hE : Real.cos β = 0 ∨ x = 0) (hB : Real.sin β = 0 ∨ x = 0) : x = 0 := by
  by_contra hx
  have hh := Real.sin_sq_add_cos_sq β
  norm_num [hE.resolve_right hx, hB.resolve_right hx] at hh

/-- At any point of strictly positive Reissner–Nordström radius, even a constant duality
rotation can make the Maxwell field vanish only when the charge is zero. -/
theorem NoHair.rn_charge_zero_at_field_zero (m e β : ℝ) (y : E4) (hy : 0 < ksRadius 0 y)
    (hzero : Real.cos β • kerrNewmanField 0 e y +
      Real.sin β • hodgeDual (kerrNewmanMetric m 0 e y) (kerrNewmanField 0 e y) = 0) : e = 0 := by
  let r := ksRadius 0 y
  let W := Wf 0 y
  let n := ksNull 0 y
  let u := r ^ 4 * W ^ 3 * e
  let vol := Real.sqrt |(kerrNewmanMetric m 0 e y).det|
  have hE (i j : Fin 4) :
      kerrNewmanField 0 e y i j = FA 0 e r (n 1) (n 2) (n 3) W i j := rnField e y hy i j
  have hB (i j : Fin 4) : hodgeDual (kerrNewmanMetric m 0 e y) (kerrNewmanField 0 e y) i j =
      (1 / 2 : ℝ) * vol * ((leviCivita i j 1 0 - leviCivita i j 0 1) * (u * n 1) +
        (leviCivita i j 2 0 - leviCivita i j 0 2) * (u * n 2) +
        (leviCivita i j 3 0 - leviCivita i j 0 3) * (u * n 3)) := by
    change (1 / 2 : ℝ) * vol * (∑ k, ∑ l, leviCivita i j k l *
        raiseBoth (kerrNewmanMetric m 0 e) (kerrNewmanField 0 e) y k l) = _
    have hup (k l : Fin 4) : raiseBoth (kerrNewmanMetric m 0 e) (kerrNewmanField 0 e) y k l =
        FupA 0 m e r (n 1) (n 2) (n 3) W k l := rnRaisedField m e y hy k l
    simp only [hup, Fin.sum_univ_four]
    simp [FupA, Fu01, Fu02, Fu03, Fu12, Fu13, Fu23, u]
    left
    ring
  have hcomponent (i j : Fin 4) : Real.cos β * FA 0 e r (n 1) (n 2) (n 3) W i j +
      Real.sin β * ((1 / 2 : ℝ) * vol * ((leviCivita i j 1 0 - leviCivita i j 0 1) * (u * n 1) +
        (leviCivita i j 2 0 - leviCivita i j 0 2) * (u * n 2) +
        (leviCivita i j 3 0 - leviCivita i j 0 3) * (u * n 3))) = 0 := by
    rw [← hE i j, ← hB i j]
    exact congrArg (fun A : Matrix (Fin 4) (Fin 4) ℝ => A i j) hzero
  have h231 : leviCivita 2 3 0 1 = 1 ∧ leviCivita 2 3 1 0 = -1 :=
    oriented_eps (Equiv.swap 0 2 * Equiv.swap 1 3) (by simp)
  have h312 : leviCivita 3 1 0 2 = 1 ∧ leviCivita 3 1 2 0 = -1 :=
    oriented_eps (Equiv.swap 0 2 * Equiv.swap 0 3) (by simp)
  have h123 : leviCivita 1 2 0 3 = 1 ∧ leviCivita 1 2 3 0 = -1 :=
    oriented_eps (Equiv.swap 0 1 * Equiv.swap 1 2) (by simp)
  have hdet : (kerrNewmanMetric m 0 e y).det ≠ 0 :=
    Matrix.det_ne_zero_of_right_inverse (mul_inv_KS (ksProfile m 0 e y) _ (ks_null 0 y hy))
  have hv : vol ≠ 0 := (Real.sqrt_pos.2 (abs_pos.mpr hdet)).ne'
  by_contra he
  have hW : 0 < W := by
    simp only [W, Wf, zero_pow (by decide : 2 ≠ 0), zero_mul, add_zero]
    exact one_div_pos.mpr (sq_pos_of_pos hy)
  have hu : u ≠ 0 := mul_ne_zero (mul_ne_zero (pow_ne_zero 4 hy.ne') (pow_ne_zero 3 hW.ne')) he
  have hrel : n 1 ^ 2 + n 2 ^ 2 + n 3 ^ 2 = 1 := ks_rel 0 y hy
  have E1 := hcomponent 0 1
  have E2 := hcomponent 0 2
  have E3 := hcomponent 0 3
  have B1 := hcomponent 2 3
  have B2 := hcomponent 3 1
  have B3 := hcomponent 1 2
  have hr : r ≠ 0 := hy.ne'
  simp [FA, Fc01, Fc02, Fc03, Fc12, Fc13, Fc23, epsAC, epsAD, epsBC, epsBD,
    h231.1, h231.2, h312.1, h312.2, h123.1, h123.2] at E1 E2 E3 B1 B2 B3
  norm_num [hr, hW.ne', he, hv, hu] at E1 E2 E3 B1 B2 B3
  norm_num [pair_forces_zero β _ E1 B1, pair_forces_zero β _ E2 B2,
    pair_forces_zero β _ E3 B3] at hrel

open scoped ContDiff Manifold Topology
open Set Filter

private theorem bilinear_zero_of_basis_pullback (B : E4 →L[ℝ] E4 →L[ℝ] ℝ)
    (L : E4 →L[ℝ] E4) (hL : Function.Surjective L)
    (h : ∀ i j, B (L (coordBasis i)) (L (coordBasis j)) = 0) : B = 0 := by
  have hexpand (x : E4) : ∑ i, x i • coordBasis i = x := by
    simpa only [EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply, coordBasis] using
      (EuclideanSpace.basisFun (Fin 4) ℝ).sum_repr x
  ext v w
  obtain ⟨a, rfl⟩ := hL v
  obtain ⟨c, rfl⟩ := hL w
  calc
    B (L a) (L c) = B (L (∑ i, a i • coordBasis i)) (L (∑ i, c i • coordBasis i)) := by
      rw [hexpand, hexpand]
    _ = 0 := by simp [map_sum, map_smul, sum_apply, smul_apply, h]

private theorem chart_derivative_surjective {M : Type*} [TopologicalSpace M] [ChartedSpace E4 M]
    [IsManifold 𝓘(ℝ, E4) ∞ M] {U : Set E4} {D : Set M} {Ψ : E4 → M}
    (hU : IsOpen U) (hD : IsOpen D) (h : IsDiffeoOnto Ψ U D) (y : E4) (hy : y ∈ U) :
    Function.Surjective (mfderiv 𝓘(ℝ, E4) 𝓘(ℝ, E4) Ψ y) := by
  obtain ⟨χ, hmap, hinv, hleft, hright, hs, ht⟩ := h
  have hx := hmap hy
  have hcomp : (Ψ ∘ χ) =ᶠ[𝓝 (Ψ y)] id :=
    Filter.mem_of_superset (hD.mem_nhds hx) (fun _ hz => hright hz)
  have hf := ((hs _ (hinv hx)).contMDiffAt (hU.mem_nhds (hinv hx))).mdifferentiableAt (by simp)
  have hi := ((ht _ hx).contMDiffAt (hD.mem_nhds hx)).mdifferentiableAt (by simp)
  have hder : mfderiv 𝓘(ℝ, E4) 𝓘(ℝ, E4) (Ψ ∘ χ) (Ψ y) =
      ContinuousLinearMap.id ℝ (TangentSpace 𝓘(ℝ, E4) (Ψ y)) := hcomp.mfderiv_eq.trans mfderiv_id
  rw [mfderiv_comp _ hf hi, hleft hy] at hder
  intro v
  refine ⟨mfderiv 𝓘(ℝ, E4) 𝓘(ℝ, E4) χ (Ψ y) v, ?_⟩
  exact DFunLike.congr_fun hder v

/-- A diffeomorphism between open regions preserves and reflects tensor zeros. -/
theorem NoHair.pullbackCoeffs_zero_iff_on_chart {M : Type*}
    [TopologicalSpace M] [ChartedSpace E4 M] [IsManifold 𝓘(ℝ, E4) ∞ M]
    (F : BilinField M) {U : Set E4} {D : Set M} {Ψ : E4 → M}
    (hU : IsOpen U) (hD : IsOpen D) (h : IsDiffeoOnto Ψ U D) {y : E4} (hy : y ∈ U) :
    pullbackCoeffs F Ψ y = 0 ↔ F (Ψ y) = 0 := by
  constructor
  · intro hp
    apply bilinear_zero_of_basis_pullback _ _ (chart_derivative_surjective hU hD h y hy)
    intro i j
    exact congrArg (fun A : Matrix (Fin 4) (Fin 4) ℝ => A i j) hp
  · intro hz
    ext i j
    exact DFunLike.congr_fun (DFunLike.congr_fun hz _) _

/-- The zero set of the Faraday tensor on any open Reissner–Nordström exterior
is either empty or the entire exterior, including after the allowed duality rotation. -/
theorem NoHair.not_rn_doc_of_mixed_field_zeros {M : Type*}
    [TopologicalSpace M] [ChartedSpace E4 M] [IsManifold 𝓘(ℝ, E4) ∞ M]
    (g F : BilinField M) (D : Set M) (hD : IsOpen D)
    (hz : ∃ x ∈ D, F x = 0) (hnz : ∃ x ∈ D, F x ≠ 0) :
    ¬ ∃ m e : ℝ, IsKerrNewmanBlackHoleParams m 0 e ∧ IsKerrNewmanDOC g F D m 0 e := by
  rintro ⟨m, e, hp, β, Ψ, hdif, hfields⟩
  have hex := hdif
  obtain ⟨χ, _, hinv, _, hright, _, _⟩ := hex
  obtain ⟨x, hx, hFx⟩ := hz
  have hxy := hinv hx
  have hpos : 0 < ksRadius 0 (χ x) :=
    lt_trans (add_pos_of_pos_of_nonneg hp.1 (Real.sqrt_nonneg _)) hxy
  have hU : IsOpen (kerrNewmanDOC m 0 e) := isOpen_lt continuous_const (continuous_ksRadius 0)
  have hF : F (Ψ (χ x)) = 0 := (congrArg (fun z : M => F z = 0) (hright hx)).mpr hFx
  have hzero := (pullbackCoeffs_zero_iff_on_chart F hU hD hdif hxy).mpr hF
  have he := rn_charge_zero_at_field_zero m e β (χ x) hpos ((hfields _ hxy).2.symm.trans hzero)
  subst e
  obtain ⟨z, hz, hFz⟩ := hnz
  have hzy := hinv hz
  have hzeroF : kerrNewmanField 0 0 (χ z) = 0 := by
    ext i j
    simp [kerrNewmanField, kerrNewmanPotential, coordPartial]
  have hzeroStar : hodgeDual (kerrNewmanMetric m 0 0 (χ z)) 0 = 0 := by
    ext i j
    simp [hodgeDual]
  have hpull : pullbackCoeffs F Ψ (χ z) = 0 := by
    rw [(hfields _ hzy).2, hzeroF, hzeroStar, smul_zero, smul_zero, zero_add]
  have hvan := (pullbackCoeffs_zero_iff_on_chart F hU hD hdif hzy).mp hpull
  exact hFz ((congrArg (fun p : M => F p = 0) (hright hz)).mp hvan)

/-! The electrostatic potential of the equal-mass Majumdar–Papapetrou exterior, with
centres at spatial coordinates (−1,0,0) and (1,0,0). Hartle and Hawking (1972), §II,
equations (2.1)–(2.8). The Maxwell two-form in this chart is d(Φ dt). -/

open NoHair NoHair.KNE

namespace NoHair.TwoCentre

noncomputable section

private lemma axis_x (a : ℝ) : axis a 1 = a := rfl
private lemma axis_y (a : ℝ) : axis a 2 = 0 := rfl
private lemma axis_z (a : ℝ) : axis a 3 = 0 := rfl

private theorem sqrtCP {f : E4 → ℝ} {y : E4} {df : Fin 4 → ℝ}
    (h : HasCP f y df) (hne : f y ≠ 0) :
    HasCP (fun z => Real.sqrt (f z)) y (fun i => df i / (2 * Real.sqrt (f y))) := by
  refine ⟨h.diff.sqrt hne, ?_⟩
  intro i
  have hn : f (y + (0 : ℝ) • coordBasis i) ≠ 0 := by simpa using hne
  simpa only [zero_smul, add_zero] using (h.line i).sqrt hn

private theorem inverseDistanceCP (a c : ℝ) (hac : a ≠ c) :
    HasCP (inverseDistance c) (axis a)
      (fun k => -((a - c) * coordBasis k 1) / |a - c| ^ 3) := by
  have hval : squaredDistance c (axis a) = (a - c) ^ 2 := by
    simp [squaredDistance, axis_x, axis_y, axis_z]
  have habs : |a - c| ≠ 0 := abs_ne_zero.mpr (sub_ne_zero.mpr hac)
  have hsqrt : Real.sqrt (squaredDistance c (axis a)) = |a - c| := by
    rw [hval, Real.sqrt_sq_eq_abs]
  have hd : HasCP (squaredDistance c) (axis a) (fun k => 2 * (a - c) * coordBasis k 1) := by
    have h := ((((hasCP_coord (axis a) 1).sub (HasCP.cst c _)).pow 2).add
      ((hasCP_coord (axis a) 2).pow 2)).add ((hasCP_coord (axis a) 3).pow 2)
    apply h.congr_d
    intro k
    simp [axis_x, axis_y, axis_z]
  have hr := sqrtCP hd (hval ▸ pow_ne_zero 2 (sub_ne_zero.mpr hac))
  have h := (HasCP.cst 1 (axis a)).div hr (hsqrt ▸ habs)
  apply h.congr_d
  intro k
  dsimp only
  rw [hsqrt]
  field_simp [habs]
  ring

private theorem electricPotentialCP (a : ℝ) (hl : a ≠ -1) (hr : a ≠ 1)
    (hU : harmonicPotential (axis a) ≠ 0) :
    HasCP electricPotential (axis a) (fun k =>
      -(-((a - -1) * coordBasis k 1) / |a - -1| ^ 3 +
        -((a - 1) * coordBasis k 1) / |a - 1| ^ 3) / harmonicPotential (axis a) ^ 2) := by
  have hu := ((HasCP.cst 1 (axis a)).add (inverseDistanceCP a (-1) hl)).add
    (inverseDistanceCP a 1 hr)
  apply ((HasCP.cst 1 (axis a)).div hu hU).congr_d
  intro k
  simp [harmonicPotential]

/-- Both points are regular exterior points of the punctured spatial domain. -/
theorem field_zero_and_nonzero : field (axis 0) = 0 ∧ field (axis 2) 0 1 = -(10 / 49 : ℝ) := by
  have val0 : harmonicPotential (axis 0) = 3 := by
    norm_num [harmonicPotential, inverseDistance, squaredDistance, axis_x, axis_y, axis_z]
  have val2 : harmonicPotential (axis 2) = 7 / 3 := by
    norm_num [harmonicPotential, inverseDistance, squaredDistance, axis_x, axis_y, axis_z]
  have h0 := electricPotentialCP 0 (by norm_num) (by norm_num) (val0 ▸ by norm_num)
  have h2 := electricPotentialCP 2 (by norm_num) (by norm_num) (val2 ▸ by norm_num)
  have hzero (k) : coordPartial electricPotential k (axis 0) = 0 := by
    rw [h0.eq k, val0]
    norm_num
  refine ⟨?_, ?_⟩
  · ext i j
    simp [field, hzero]
  · simp only [field, show (1 : Fin 4) ≠ 0 by decide, if_false, if_true, zero_sub]
    rw [h2.eq 1, val2]
    norm_num [coordBasis, PiLp.single_apply]

end
end NoHair.TwoCentre

open scoped ContDiff Manifold
open Set NoHair

namespace NoHair.TwoCentre

private theorem isOpen_exterior : IsOpen exterior := by
  have h (c : ℝ) : Continuous (squaredDistance c) := by unfold squaredDistance; fun_prop
  exact (isOpen_lt (continuous_const (y := (0 : ℝ))) (h (-1))).inter
    (isOpen_lt continuous_const (h 1))

private theorem axis_mem_exterior (a : ℝ) (hl : a ≠ -1) (hr : a ≠ 1) : axis a ∈ exterior := by
  have hx : (axis a) 1 = a := rfl
  have hy : (axis a) 2 = 0 := rfl
  have hz : (axis a) 3 = 0 := rfl
  simpa [exterior, squaredDistance, hx, hy, hz] using
    And.intro (sq_pos_of_ne_zero (sub_ne_zero.mpr hl)) (sq_pos_of_ne_zero (sub_ne_zero.mpr hr))

end NoHair.TwoCentre

open NoHair NoHair.TwoCentre Set
open scoped ContDiff Manifold

theorem solution {M : Type*} [TopologicalSpace M] [ChartedSpace E4 M]
    [IsManifold 𝓘(ℝ, E4) ∞ M] (g F : BilinField M) (D : Set M)
    (hD : IsOpen D) (Ψ : E4 → M) (hΨ : IsDiffeoOnto Ψ exterior D)
    (hfield : ∀ y ∈ exterior, pullbackCoeffs F Ψ y = field y) :
    ¬ ∃ m e : ℝ, IsKerrNewmanBlackHoleParams m 0 e ∧ IsKerrNewmanDOC g F D m 0 e := by
  have h0 := axis_mem_exterior 0 (by norm_num) (by norm_num)
  have h2 := axis_mem_exterior 2 (by norm_num) (by norm_num)
  have hex := hΨ
  obtain ⟨_, hmap, _⟩ := hex
  apply not_rn_doc_of_mixed_field_zeros g F D hD
  · refine ⟨Ψ (axis 0), hmap h0, ?_⟩
    exact (pullbackCoeffs_zero_iff_on_chart F isOpen_exterior hD hΨ h0).mp
      ((hfield _ h0).trans field_zero_and_nonzero.1)
  · refine ⟨Ψ (axis 2), hmap h2, ?_⟩
    intro hz
    have hmat := (hfield _ h2).symm.trans
      ((pullbackCoeffs_zero_iff_on_chart F isOpen_exterior hD hΨ h2).mpr hz)
    have hentry := congrArg (fun A : Matrix (Fin 4) (Fin 4) ℝ => A 0 1) hmat
    change field (axis 2) 0 1 = 0 at hentry
    rw [field_zero_and_nonzero.2] at hentry
    norm_num at hentry

