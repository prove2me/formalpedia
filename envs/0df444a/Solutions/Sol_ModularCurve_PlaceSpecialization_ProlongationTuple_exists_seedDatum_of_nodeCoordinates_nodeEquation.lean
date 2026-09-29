-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.ProlongationTuple.exists_seedDatum_of_nodeCoordinates_nodeEquation
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/0f38e2f5-7dfd-5356-9219-503f220493ba

import Definitions.Def_ModularCurve_NodeLocalizedPlaces
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_seedDatum_of_nodeCoordinates_nodeEquation
set_option synthInstance.maxHeartbeats 1600000
set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve
open ModularCurve.PlaceSpecialization ModularCurve.PlaceSpecialization.ProlongationTuple

noncomputable section

namespace P2mWs18BfV3

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
  {k : Type*} [Field k] [CharP k q] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
  {P : PlaceSpecialization A q N data hKr k red hα hβ} (R : ProlongationTuple P)

private theorem ord_eq_zero_of_mem_of_inv_mem (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) {f : ↥(modularFunctionFieldBar (N * q))}
    (hf : f ∈ V.toValuationSubring) (hf' : f⁻¹ ∈ V.toValuationSubring) : V.ord f = 0 := by
  have h1 := V.ord_nonneg_of_mem hf
  have h2 := V.ord_nonneg_of_mem hf'
  rw [Place.ord_inv] at h2
  omega

private theorem ord_algebraMap_eq_zero (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) {c : AlgebraicClosure ℚ} (hc : c ≠ 0) :
    V.ord (algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) c) = 0 :=
  ord_eq_zero_of_mem_of_inv_mem V (V.algebraMap_mem' c) (by rw [← map_inv₀]; exact V.algebraMap_mem' c⁻¹)

private theorem coe_units_inv {S : Subring ↥(modularFunctionFieldBar (N * q))} (u : (↥S)ˣ) : (((u⁻¹ : (↥S)ˣ) : ↥S) : ↥(modularFunctionFieldBar (N * q))) = ((u : ↥S) : ↥(modularFunctionFieldBar (N * q)))⁻¹ := by
  have h1 := congrArg (fun z : ↥S => (z : ↥(modularFunctionFieldBar (N * q)))) u.mul_inv
  simp only [Subring.coe_mul, OneMemClass.coe_one] at h1
  exact eq_inv_of_mul_eq_one_right h1

private theorem coe_units_inv_vs {S : ValuationSubring ↥(modularFunctionFieldBar (N * q))} (u : (↥S)ˣ) : (((u⁻¹ : (↥S)ˣ) : ↥S) : ↥(modularFunctionFieldBar (N * q))) = ((u : ↥S) : ↥(modularFunctionFieldBar (N * q)))⁻¹ := by
  have h1 := congrArg (fun z : ↥S => (z : ↥(modularFunctionFieldBar (N * q)))) u.mul_inv
  simp only [MulMemClass.coe_mul, OneMemClass.coe_one] at h1
  exact eq_inv_of_mul_eq_one_right h1

private theorem residueSnd_ne_zero_of_isUnit {f : ↥R.R₂.integers} (hf : IsUnit f) : R.R₂.residue f ≠ 0 := by
  intro h0
  have hmem : f ∈ RingHom.ker R.R₂.residue := h0
  rw [R.R₂.ker_residue] at hmem
  exact (IsLocalRing.mem_maximalIdeal _).mp hmem hf

omit [Fact q.Prime] [NeZero N] [CharP k q] in
private theorem cancel_aux {F : Type*} [Field F] (c a b : F) (hc : c ≠ 0) : (c * a) * (c * b)⁻¹ = a * b⁻¹ := by
  rw [mul_inv, mul_mul_mul_comm, mul_inv_cancel₀ hc, one_mul]

section Node

variable [IsAlgClosed k] {K : IntermediateField ℚ (AlgebraicClosure ℚ)} {w : Place k (modularFunctionFieldC k N)}
  (c : R.NodeCoordinates K w) (e : ℕ) (u : ↥(R.nodeIntegersOver K w)) (hu : IsUnit u)
  (hxy : c.x * c.y = R.nodeConst K w ((q : ℕ) : ↥(NodeLocalized.coeffSubring A K)) ^ e * u)

include hxy in

private theorem coe_x_mul_coe_y :
    ((c.x : ↥(R.nodeIntegersOver K w)) : ↥(modularFunctionFieldBar (N * q))) * ((c.y : ↥(R.nodeIntegersOver K w)) : ↥(modularFunctionFieldBar (N * q)))
      = algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) ((q : ℕ) : AlgebraicClosure ℚ) ^ e * ((u : ↥(R.nodeIntegersOver K w)) : ↥(modularFunctionFieldBar (N * q))) := by
  have h := congrArg (fun z : ↥(R.nodeIntegersOver K w) => (z : ↥(modularFunctionFieldBar (N * q)))) hxy
  simp only [Subring.coe_mul, SubmonoidClass.coe_pow, coe_nodeConst] at h
  convert h using 3 <;> try rfl

include hu in

private theorem inv_mem_of_isUnit : ((u : ↥(R.nodeIntegersOver K w)) : ↥(modularFunctionFieldBar (N * q)))⁻¹ ∈ R.nodeIntegersOver K w := by
  obtain ⟨uu, huu⟩ := hu
  rw [← huu, ← coe_units_inv]
  exact SetLike.coe_mem _

include hu in
private theorem coe_u_ne_zero : ((u : ↥(R.nodeIntegersOver K w)) : ↥(modularFunctionFieldBar (N * q))) ≠ 0 := by
  intro h0
  have h1 : ((u : ↥(R.nodeIntegersOver K w)) : ↥(modularFunctionFieldBar (N * q))) * ((u : ↥(R.nodeIntegersOver K w)) : ↥(modularFunctionFieldBar (N * q)))⁻¹ ∈ R.nodeIntegersOver K w :=
    mul_mem u.2 (inv_mem_of_isUnit R u hu)
  obtain ⟨uu, huu⟩ := hu
  have : (uu : ↥(R.nodeIntegersOver K w)) = 0 := by
    rw [huu]; exact Subtype.ext h0
  exact uu.ne_zero this

private theorem y_mem_nodeIntegers : ((c.y : ↥(R.nodeIntegersOver K w)) : ↥(modularFunctionFieldBar (N * q))) ∈ R.nodeIntegers w := c.y.2.1

private theorem y_residueFst_ne_zero :
    ∃ h : ((c.y : ↥(R.nodeIntegersOver K w)) : ↥(modularFunctionFieldBar (N * q))) ∈ R.R₁.integers, R.R₁.residue ⟨(c.y : ↥(modularFunctionFieldBar (N * q))), h⟩ ≠ 0 := by
  refine ⟨c.y.2.1.1, fun h0 => c.nodeResidue₁_y_ne_zero ?_⟩
  rw [nodeResidue₁_apply, residue₁_apply]
  change R.ι (R.R₁.residue ⟨(c.y : ↥(modularFunctionFieldBar (N * q))), c.y.2.1.1⟩) = 0
  rw [h0, map_zero]

include hu hxy in

private theorem ord_y_eq_zero (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) (hV : P.reduceFst V = w) :
    V.ord ((c.y : ↥(R.nodeIntegersOver K w)) : ↥(modularFunctionFieldBar (N * q))) = 0 := by
  have hq0 : ((q : ℕ) : AlgebraicClosure ℚ) ≠ 0 := by exact_mod_cast (Fact.out : q.Prime).ne_zero
  have hQ : V.ord (algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) ((q : ℕ) : AlgebraicClosure ℚ) ^ e) = 0 := by
    rw [← map_pow]; exact ord_algebraMap_eq_zero V (pow_ne_zero _ hq0)
  have hU : V.ord ((u : ↥(R.nodeIntegersOver K w)) : ↥(modularFunctionFieldBar (N * q))) = 0 :=
    ord_eq_zero_of_mem_of_inv_mem V (u.2.1.2.2 V hV) ((inv_mem_of_isUnit R u hu).1.2.2 V hV)
  have hx0 : ((c.x : ↥(R.nodeIntegersOver K w)) : ↥(modularFunctionFieldBar (N * q))) ≠ 0 := by
    intro h0
    have h := coe_x_mul_coe_y R c e u hxy
    rw [h0, zero_mul] at h
    exact (mul_ne_zero (pow_ne_zero _ ((map_ne_zero _).mpr hq0)) (coe_u_ne_zero R u hu)) h.symm
  have hy0 : ((c.y : ↥(R.nodeIntegersOver K w)) : ↥(modularFunctionFieldBar (N * q))) ≠ 0 := by
    intro h0
    have h := coe_x_mul_coe_y R c e u hxy
    rw [h0, mul_zero] at h
    exact (mul_ne_zero (pow_ne_zero _ ((map_ne_zero _).mpr hq0)) (coe_u_ne_zero R u hu)) h.symm
  have hsum := congrArg V.ord (coe_x_mul_coe_y R c e u hxy)
  rw [V.ord_mul hx0 hy0, V.ord_mul (pow_ne_zero _ ((map_ne_zero _).mpr hq0)) (coe_u_ne_zero R u hu), hQ, hU] at hsum
  have hx := R.ord_nonneg_of_mem_nodeIntegers c.x.2.1 hV
  have hy := R.ord_nonneg_of_mem_nodeIntegers c.y.2.1 hV
  omega

include hu hxy in

private theorem exists_units_coe_y_eq :
    ∃ G : (↥R.R₂.integers)ˣ, ((c.y : ↥(R.nodeIntegersOver K w)) : ↥(modularFunctionFieldBar (N * q)))
      = algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) ((q : ℕ) : AlgebraicClosure ℚ) ^ e * (((G : ↥R.R₂.integers) : ↥(modularFunctionFieldBar (N * q)))) := by
  have hq0 : ((q : ℕ) : AlgebraicClosure ℚ) ≠ 0 := by exact_mod_cast (Fact.out : q.Prime).ne_zero

  have hx2 : ((c.x : ↥(R.nodeIntegersOver K w)) : ↥(modularFunctionFieldBar (N * q))) ∈ R.R₂.integers := c.x.2.1.2.1
  have hxres : R.R₂.residue ⟨(c.x : ↥(modularFunctionFieldBar (N * q))), hx2⟩ ≠ 0 := by
    intro h0
    apply c.nodeResidue₂_x_ne_zero
    rw [nodeResidue₂_apply, residue₂_apply]
    change R.ι (R.R₂.residue ⟨(c.x : ↥(modularFunctionFieldBar (N * q))), hx2⟩) = 0
    rw [h0, map_zero]
  obtain ⟨xU, hxU⟩ := R.R₂.isUnit_of_residue_ne_zero hxres

  have hu2 : ((u : ↥(R.nodeIntegersOver K w)) : ↥(modularFunctionFieldBar (N * q))) ∈ R.R₂.integers := u.2.1.2.1
  have hu2' : ((u : ↥(R.nodeIntegersOver K w)) : ↥(modularFunctionFieldBar (N * q)))⁻¹ ∈ R.R₂.integers := (inv_mem_of_isUnit R u hu).1.2.1
  let uU : (↥R.R₂.integers)ˣ :=
    ⟨⟨(u : ↥(modularFunctionFieldBar (N * q))), hu2⟩, ⟨(u : ↥(modularFunctionFieldBar (N * q)))⁻¹, hu2'⟩, Subtype.ext (mul_inv_cancel₀ (coe_u_ne_zero R u hu)),
      Subtype.ext (inv_mul_cancel₀ (coe_u_ne_zero R u hu))⟩
  refine ⟨uU * xU⁻¹, ?_⟩
  have hx0 : ((c.x : ↥(R.nodeIntegersOver K w)) : ↥(modularFunctionFieldBar (N * q))) ≠ 0 := by
    intro h0
    have : (xU : ↥R.R₂.integers) = 0 := by rw [hxU]; exact Subtype.ext h0
    exact xU.ne_zero this
  have hxinv : (((xU⁻¹ : (↥R.R₂.integers)ˣ) : ↥R.R₂.integers) : ↥(modularFunctionFieldBar (N * q))) = ((c.x : ↥(R.nodeIntegersOver K w)) : ↥(modularFunctionFieldBar (N * q)))⁻¹ := by
    rw [coe_units_inv_vs, hxU]
  rw [Units.val_mul, MulMemClass.coe_mul, hxinv]
  change _ = _ * (((u : ↥(R.nodeIntegersOver K w)) : ↥(modularFunctionFieldBar (N * q))) * ((c.x : ↥(R.nodeIntegersOver K w)) : ↥(modularFunctionFieldBar (N * q)))⁻¹)
  have h := coe_x_mul_coe_y R c e u hxy
  symm
  calc algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) ((q : ℕ) : AlgebraicClosure ℚ) ^ e *
        (((u : ↥(R.nodeIntegersOver K w)) : ↥(modularFunctionFieldBar (N * q))) * ((c.x : ↥(R.nodeIntegersOver K w)) : ↥(modularFunctionFieldBar (N * q)))⁻¹)
      = (((c.x : ↥(R.nodeIntegersOver K w)) : ↥(modularFunctionFieldBar (N * q))) * ((c.y : ↥(R.nodeIntegersOver K w)) : ↥(modularFunctionFieldBar (N * q))))
          * ((c.x : ↥(R.nodeIntegersOver K w)) : ↥(modularFunctionFieldBar (N * q)))⁻¹ := by rw [h, mul_assoc]
    _ = ((c.y : ↥(R.nodeIntegersOver K w)) : ↥(modularFunctionFieldBar (N * q))) := by
          rw [mul_comm ((c.x : ↥(R.nodeIntegersOver K w)) : ↥(modularFunctionFieldBar (N * q))), mul_assoc, mul_inv_cancel₀ hx0, mul_one]

end Node

private theorem hvert_aux (Q : ↥(modularFunctionFieldBar (N * q))) (hQ0 : Q ≠ 0) (G G' : (↥R.R₂.integers)ˣ)
    (y y' : ↥(modularFunctionFieldBar (N * q))) (m m' d d' L : ℕ)
    (hy : y = Q ^ m * (((G : ↥R.R₂.integers) : ↥(modularFunctionFieldBar (N * q)))))
    (hy' : y' = Q ^ m' * (((G' : ↥R.R₂.integers) : ↥(modularFunctionFieldBar (N * q)))))
    (hd : m * d = L) (hd' : m' * d' = L) :
    ∃ h : y ^ d * (y' ^ d')⁻¹ ∈ R.R₂.integers, R.R₂.residue ⟨y ^ d * (y' ^ d')⁻¹, h⟩ ≠ 0 := by
  subst hy hy'
  have hGval : (((G ^ d * (G' ^ d')⁻¹ : (↥R.R₂.integers)ˣ) : ↥R.R₂.integers) : ↥(modularFunctionFieldBar (N * q)))
      = (((G : ↥R.R₂.integers) : ↥(modularFunctionFieldBar (N * q)))) ^ d
        * ((((G' : ↥R.R₂.integers) : ↥(modularFunctionFieldBar (N * q)))) ^ d')⁻¹ := by
    rw [Units.val_mul, MulMemClass.coe_mul, coe_units_inv_vs, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val,
      SubmonoidClass.coe_pow, SubmonoidClass.coe_pow]
  have key : (Q ^ m * (((G : ↥R.R₂.integers) : ↥(modularFunctionFieldBar (N * q))))) ^ d
        * ((Q ^ m' * (((G' : ↥R.R₂.integers) : ↥(modularFunctionFieldBar (N * q))))) ^ d')⁻¹
      = (((G ^ d * (G' ^ d')⁻¹ : (↥R.R₂.integers)ˣ) : ↥R.R₂.integers) : ↥(modularFunctionFieldBar (N * q))) := by
    rw [hGval, mul_pow, mul_pow, ← pow_mul, ← pow_mul, hd, hd']
    exact cancel_aux (Q ^ L) _ _ (pow_ne_zero _ hQ0)
  have hmem : (Q ^ m * (((G : ↥R.R₂.integers) : ↥(modularFunctionFieldBar (N * q))))) ^ d
        * ((Q ^ m' * (((G' : ↥R.R₂.integers) : ↥(modularFunctionFieldBar (N * q))))) ^ d')⁻¹ ∈ R.R₂.integers := by
    rw [key]; exact SetLike.coe_mem _
  refine ⟨hmem, ?_⟩
  have hsub : (⟨_, hmem⟩ : ↥R.R₂.integers) = ((G ^ d * (G' ^ d')⁻¹ : (↥R.R₂.integers)ˣ) : ↥R.R₂.integers) :=
    Subtype.ext key
  rw [hsub]
  exact residueSnd_ne_zero_of_isUnit R (Units.isUnit _)

end P2mWs18BfV3

end

open AlgebraicCurve IsLocalRing ModularCurve
open ModularCurve.PlaceSpecialization ModularCurve.PlaceSpecialization.ProlongationTuple
open P2mWs18BfV3 in
theorem solution
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    {P : PlaceSpecialization A q N data hKr k red hα hβ}
    (R : ProlongationTuple P) [IsAlgClosed k] [DecidableEq k] (hqN : ¬ q ∣ N)
    (W : Finset (Place k (modularFunctionFieldC k N)))
    (Ks : ↥W → IntermediateField ℚ (AlgebraicClosure ℚ)) [∀ w : ↥W, FiniteDimensional ℚ (Ks w)]
    (cs : ∀ w : ↥W, R.NodeCoordinates (Ks w) (w : Place k (modularFunctionFieldC k N)))
    (e : Place k (modularFunctionFieldC k N) → ℕ)
    (us : ∀ w : ↥W, ↥(R.nodeIntegersOver (Ks w) (w : Place k (modularFunctionFieldC k N))))
    (hus : ∀ w : ↥W, IsUnit (us w))
    (hxy : ∀ w : ↥W, (cs w).x * (cs w).y =
      R.nodeConst (Ks w) (w : Place k (modularFunctionFieldC k N))
        ((q : ℕ) : ↥(NodeLocalized.coeffSubring A (Ks w))) ^ e (w : Place k (modularFunctionFieldC k N)) * us w) :
    ∃ (y : Place k (modularFunctionFieldC k N) → ↥(modularFunctionFieldBar (N * q)))
      (n : Place k (modularFunctionFieldC k N) → ℕ),
      (∀ (w) (hw : w ∈ W), y w = ((cs ⟨w, hw⟩).y : ↥(modularFunctionFieldBar (N * q)))) ∧
      (∀ w ∈ W, n w = W.lcm e / e w) ∧
      (∀ w ∈ W, y w ∈ R.nodeIntegers w) ∧
      (∀ w ∈ W, ∃ h : y w ∈ R.R₁.integers, R.R₁.residue ⟨y w, h⟩ ≠ 0) ∧
      (∀ w ∈ W, ∀ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)),
        P.reduceFst V = w → V.ord (y w) = 0) ∧
      (∀ w ∈ W, ∀ w' ∈ W,
        ∃ h : y w ^ n w * (y w' ^ n w')⁻¹ ∈ R.R₂.integers, R.R₂.residue ⟨y w ^ n w * (y w' ^ n w')⁻¹, h⟩ ≠ 0) := by
  classical
  have hq0 : ((q : ℕ) : AlgebraicClosure ℚ) ≠ 0 := by exact_mod_cast (Fact.out : q.Prime).ne_zero
  let y : Place k (modularFunctionFieldC k N) → ↥(modularFunctionFieldBar (N * q)) :=
    fun v => if h : v ∈ W then ((cs ⟨v, h⟩).y : ↥(modularFunctionFieldBar (N * q))) else 1
  let n : Place k (modularFunctionFieldC k N) → ℕ := fun v => W.lcm e / e v
  have hy : ∀ (w) (hw : w ∈ W), y w = ((cs ⟨w, hw⟩).y : ↥(modularFunctionFieldBar (N * q))) := by
    intro w hw
    simp only [y, dif_pos hw]
  refine ⟨y, n, hy, fun w _ => rfl, ?_, ?_, ?_, ?_⟩
  · intro w hw
    rw [hy w hw]
    exact (cs ⟨w, hw⟩).y.2.1
  · intro w hw
    rw [hy w hw]
    exact y_residueFst_ne_zero R (cs ⟨w, hw⟩)
  · intro w hw V hV
    rw [hy w hw]
    exact ord_y_eq_zero R (cs ⟨w, hw⟩) (e w) (us ⟨w, hw⟩) (hus ⟨w, hw⟩) (hxy ⟨w, hw⟩) V hV
  · intro w hw w' hw'
    obtain ⟨G, hG⟩ := exists_units_coe_y_eq R (cs ⟨w, hw⟩) (e w) (us ⟨w, hw⟩) (hus ⟨w, hw⟩) (hxy ⟨w, hw⟩)
    obtain ⟨G', hG'⟩ := exists_units_coe_y_eq R (cs ⟨w', hw'⟩) (e w') (us ⟨w', hw'⟩) (hus ⟨w', hw'⟩) (hxy ⟨w', hw'⟩)
    have he : e w * n w = W.lcm e := Nat.mul_div_cancel' (Finset.dvd_lcm hw)
    have he' : e w' * n w' = W.lcm e := Nat.mul_div_cancel' (Finset.dvd_lcm hw')
    exact hvert_aux R (algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) ((q : ℕ) : AlgebraicClosure ℚ))
      ((map_ne_zero _).mpr hq0) G G' (y w) (y w') (e w) (e w') (n w) (n w') (W.lcm e)
      (by rw [hy w hw, hG]) (by rw [hy w' hw', hG']) he he'

end S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_seedDatum_of_nodeCoordinates_nodeEquation
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_seedDatum_of_nodeCoordinates_nodeEquation (solution)
