-- Prove2me | solution 1 for OAI.Erdos3.VectorPolynomial.allocatedAffineSourceReferenceError_small_separated_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T06:01:12.380986+00:00
-- url     : https://prove2.me/submissions/d15178e6-427a-4bd0-b873-81cbf20efb0f

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B213

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AllocatedAffineScaleEnvelope
namespace OAI

section

namespace Erdos3

theorem affineReferenceCoefficient_bounds
    {D L dlog slog P ideal Ki Cmask boundary : ℝ}
    (hD : 0 ≤ D) (hL : 0 ≤ L)
    (hdlog : dlog ≤ L) (hslog : slog ≤ L) (hP : P ≤ L)
    (hideal : ideal ≤ Real.exp L) (hKi : Ki ≤ Real.exp L)
    (hCmask0 : 0 ≤ Cmask) (hCmask : Cmask ≤ Real.exp L)
    (hb0 : 0 ≤ boundary) (hb : boundary ≤ Real.exp L)
    (axes output unselected integer : ℕ)
    (ha : (axes : ℝ) ≤ D) (ho : (output : ℝ) ≤ D)
    (hu : (unselected : ℝ) ≤ D) (hi : (integer : ℝ) ≤ D) :
    let cap := (Real.exp dlog) ^ axes
    let lip := (axes : ℝ) * Real.exp dlog * cap
    let radius := max (Real.exp P * ideal) (Real.exp slog)
    let mask := Cmask ^ axes
    let support := (2 * Real.exp slog) ^ output
    let Q := affineReferenceCoefficientLog D L
    mask ≤ Real.exp Q ∧
    mask * (2 * cap * boundary + lip * 2) * support ≤ Real.exp Q ∧
    mask * lip * support ≤ Real.exp Q ∧
    mask * (2 * radius) ^ unselected * ((2 * radius + 2) ^ integer * (Ki + lip)) ≤ Real.exp Q := by
  intro cap lip radius mask support Q
  have hDL : 0 ≤ D * L := mul_nonneg hD hL
  have hcap : cap ≤ Real.exp (D * L) :=
    pow_le_exp_mul_of_le_exp (Real.exp_pos _).le (Real.exp_le_exp.mpr hdlog) hL axes ha
  have hm : mask ≤ Real.exp (D * L) :=
    pow_le_exp_mul_of_le_exp hCmask0 hCmask hL axes ha
  have haxes : (axes : ℝ) ≤ Real.exp D := ha.trans (by linarith [Real.add_one_le_exp D])
  have hlip : lip ≤ Real.exp (D + L + D * L) := by
    calc
      _ ≤ Real.exp D * Real.exp L * Real.exp (D * L) := by dsimp [lip, cap]; gcongr
      _ = _ := by rw [← Real.exp_add, ← Real.exp_add]
  have h2 : (2 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
  have h4 : (4 : ℝ) ≤ Real.exp 4 := by linarith [Real.add_one_le_exp (4 : ℝ)]
  have hrad : radius ≤ Real.exp (2 * L) := by
    apply max_le
    · calc
        _ ≤ Real.exp P * Real.exp L := mul_le_mul_of_nonneg_left hideal (Real.exp_pos _).le
        _ ≤ Real.exp L * Real.exp L := by gcongr
        _ = _ := by rw [← Real.exp_add]; congr 1; ring
    · exact Real.exp_le_exp.mpr (by linarith)
  have hrad0 : 0 ≤ radius := (Real.exp_pos slog).le.trans (le_max_right _ _)
  have hsuppBase : 2 * Real.exp slog ≤ Real.exp (L + 2) := by
    calc
      _ ≤ Real.exp L * Real.exp 2 := by rw [mul_comm 2]; gcongr
      _ = _ := (Real.exp_add _ _).symm
  have hsupp : support ≤ Real.exp (D * (L + 2)) :=
    pow_le_exp_mul_of_le_exp (by positivity) hsuppBase (by positivity) output ho
  have hradBase : 2 * radius ≤ Real.exp (2 * L + 2) := by
    calc
      _ ≤ Real.exp (2 * L) * Real.exp 2 := by rw [mul_comm 2]; gcongr
      _ = _ := (Real.exp_add _ _).symm
  have hradPlus : 2 * radius + 2 ≤ Real.exp (2 * L + 4) := by
    have h1 : 1 ≤ Real.exp (2 * L) := Real.one_le_exp_iff.mpr (by positivity)
    calc
      _ ≤ 4 * Real.exp (2 * L) := by linarith only [hrad, h1]
      _ ≤ Real.exp (2 * L) * Real.exp 4 := by nlinarith [Real.exp_pos (2 * L)]
      _ = _ := (Real.exp_add _ _).symm
  have hru := pow_le_exp_mul_of_le_exp (mul_nonneg (by norm_num) hrad0) hradBase
    (by positivity : 0 ≤ 2 * L + 2) unselected hu
  have hri := pow_le_exp_mul_of_le_exp (by positivity : 0 ≤ 2 * radius + 2) hradPlus
    (by positivity : 0 ≤ 2 * L + 4) integer hi
  have hbl : 2 * cap * boundary ≤ Real.exp (D * L + L + 2) := by
    calc
      _ ≤ Real.exp (D * L) * Real.exp L * Real.exp 2 := by
        rw [show 2 * cap * boundary = cap * boundary * 2 by ring]
        gcongr
      _ = _ := by rw [← Real.exp_add, ← Real.exp_add]
  have hll : lip * 2 ≤ Real.exp (D + L + D * L + 2) := by
    calc
      _ ≤ Real.exp (D + L + D * L) * Real.exp 2 := by gcongr
      _ = _ := (Real.exp_add _ _).symm
  have hboundary := add_le_exp_add_one (by positivity : 0 ≤ D * L + L + 2)
    (by positivity : 0 ≤ D + L + D * L + 2) hbl hll
  have hsum := add_le_exp_add_one hL (by positivity : 0 ≤ D + L + D * L) hKi hlip
  have hlog₀ : D * L ≤ Q := by dsimp [Q, affineReferenceCoefficientLog]; nlinarith only [hDL, hD, hL]
  have hlog₁ : D * L + ((D * L + L + 2) + (D + L + D * L + 2) + 1) + D * (L + 2) ≤ Q := by
    dsimp [Q, affineReferenceCoefficientLog]; nlinarith only [hDL, hD, hL]
  have hlog₂ : D * L + (D + L + D * L) + D * (L + 2) ≤ Q := by
    dsimp [Q, affineReferenceCoefficientLog]; nlinarith only [hDL, hD, hL]
  have hlog₃ : D * L + D * (2 * L + 2) +
      (D * (2 * L + 4) + (L + (D + L + D * L) + 1)) ≤ Q := by
    dsimp [Q, affineReferenceCoefficientLog]; nlinarith only [hDL, hD, hL]
  refine ⟨hm.trans (Real.exp_le_exp.mpr hlog₀), ?_, ?_, ?_⟩
  · calc
      _ ≤ Real.exp (D * L) * Real.exp ((D * L + L + 2) + (D + L + D * L + 2) + 1) *
          Real.exp (D * (L + 2)) := by gcongr
      _ ≤ _ := by rw [← Real.exp_add, ← Real.exp_add]; exact Real.exp_le_exp.mpr hlog₁
  · calc
      _ ≤ Real.exp (D * L) * Real.exp (D + L + D * L) * Real.exp (D * (L + 2)) := by gcongr
      _ ≤ _ := by rw [← Real.exp_add, ← Real.exp_add]; exact Real.exp_le_exp.mpr hlog₂
  · by_cases hneg : Ki + lip < 0
    · exact (mul_nonpos_of_nonneg_of_nonpos (by positivity)
        (mul_nonpos_of_nonneg_of_nonpos (by positivity) hneg.le)).trans (Real.exp_pos Q).le
    · have hsum0 := le_of_not_gt hneg
      calc
        _ ≤ Real.exp (D * L) * Real.exp (D * (2 * L + 2)) *
            (Real.exp (D * (2 * L + 4)) * Real.exp (L + (D + L + D * L) + 1)) := by gcongr
        _ ≤ _ := by simp only [← Real.exp_add]; exact Real.exp_le_exp.mpr hlog₃

theorem affineReferenceError_accuracy_separated {target Q Qη mask cap lip boundary support volume Ki η ratio ε mesh : ℝ}
    (hη0 : 0 ≤ η) (hratio0 : 0 ≤ ratio) (hε0 : 0 ≤ ε) (hmesh0 : 0 ≤ mesh)
    (hcoeff : mask ≤ Real.exp Qη ∧
      mask * (2 * cap * boundary + lip * 2) * support ≤ Real.exp Q ∧
      mask * lip * support ≤ Real.exp Q ∧ mask * volume * (Ki + lip) ≤ Real.exp Q)
    (hη : η ≤ Real.exp (-(target + Qη + 4)))
    (hratio : ratio ≤ Real.exp (-(target + Q + 4)))
    (hε : ε ≤ Real.exp (-(target + Q + 4)))
    (hmesh : mesh ≤ Real.exp (-(target + Q + 4))) :
    mask * (η + ((2 * cap * boundary + lip * 2) * ratio + lip * ε) * support +
      volume * (Ki + lip) * mesh) ≤ Real.exp (-target) := by
  have hterm {c x Q : ℝ} (hc : c ≤ Real.exp Q) (hx0 : 0 ≤ x)
      (hx : x ≤ Real.exp (-(target + Q + 4))) : c * x ≤ Real.exp (-(target + 4)) := by
    calc
      _ ≤ Real.exp Q * Real.exp (-(target + Q + 4)) :=
        (mul_le_mul_of_nonneg_right hc hx0).trans (mul_le_mul_of_nonneg_left hx (Real.exp_pos _).le)
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have h₁ := hterm hcoeff.1 hη0 hη
  have h₂ := hterm hcoeff.2.1 hratio0 hratio
  have h₃ := hterm hcoeff.2.2.1 hε0 hε
  have h₄ := hterm hcoeff.2.2.2 hmesh0 hmesh
  have hsum : mask * (η + ((2 * cap * boundary + lip * 2) * ratio + lip * ε) * support +
      volume * (Ki + lip) * mesh) ≤ 4 * Real.exp (-(target + 4)) := by
    nlinarith only [h₁, h₂, h₃, h₄]
  have h4 : (4 : ℝ) ≤ Real.exp 4 := by linarith [Real.add_one_le_exp (4 : ℝ)]
  calc
    _ ≤ 4 * Real.exp (-(target + 4)) := hsum
    _ ≤ Real.exp 4 * Real.exp (-(target + 4)) := mul_le_mul_of_nonneg_right h4 (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AllocatedAffineWholeProfileComparison
namespace OAI

section

namespace Erdos3.VectorPolynomial
open MeasureTheory
open scoped BigOperators NNReal Classical

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
variable (α : Type*) [Fintype α] [DecidableEq α] (O : Fin m → Type*) [∀ j, Fintype (O j)]

local notation "grid" => allocatedGridAxis (I := I) U basis S.value
local notation "Outputs" => (Σ a : {a // ¬grid a}, O (Sigma.fst (Subtype.val a)))
local notation "select" => allocatedLongIntegerSelect B U basis S (O := O)

theorem allocatedAffineSourceReferenceError_small_separated_s2_oai
    (ρ : ℝ≥0) (P : ℝ)
    (M H : PrincipalTupleIndex
      (fun a : {a // ¬grid a} => B a.val)
      (fun a : {a // ¬grid a} => layerSamplerDegree I n a.val) → ℕ)
    {D L target η ε mesh Cmask earlyMaskLog : ℝ}
    (hearlyMask : Cmask ^ Fintype.card (LayerSamplerAxis I n) ≤ Real.exp earlyMaskLog)
    (hD : 0 ≤ D) (hL : 0 ≤ L) (hP : P ≤ L)
    (hdensity : allocatedDensityLog (G := G) B α O P ≤ L)
    (hsupport : allocatedJetSupportLog (G := G) B α O P ≤ L)
    (hideal : partitionedIdealRadius α m + 1 ≤ Real.exp L)
    (hKi : ‖(∏ o : Outputs, |R o.1.val.1|)⁻¹‖ *
      ((affineProductProfileLip Outputs ρ : ℝ) * Real.exp P) ≤ Real.exp L)
    (hCmask0 : 0 ≤ Cmask) (hCmask : Cmask ≤ Real.exp L)
    (hb0 : 0 ≤ scalarCubeGridBoundaryConstant α / volume.real (scalarCubeDomain α))
    (hb : scalarCubeGridBoundaryConstant α / volume.real (scalarCubeDomain α) ≤ Real.exp L)
    (ha : (Fintype.card (LayerSamplerAxis I n) : ℝ) ≤ D)
    (ho : (Fintype.card Outputs : ℝ) ≤ D)
    (hu : (Fintype.card (UnselectedColumn select) : ℝ) ≤ D)
    (hi : (Fintype.card {o : Outputs // allocatedLongIntegerCoordinate B U basis S (O := O) o} : ℝ) ≤ D)
    (hη0 : 0 ≤ η) (hε0 : 0 ≤ ε) (hmesh0 : 0 ≤ mesh)
    (hη : η ≤ Real.exp (-(target + earlyMaskLog + 4)))
    (hratio : (∑ j, (M j : ℝ) / H j) ≤ Real.exp (-(target + affineReferenceCoefficientLog D L + 4)))
    (hε : ε ≤ Real.exp (-(target + affineReferenceCoefficientLog D L + 4)))
    (hmesh : mesh ≤ Real.exp (-(target + affineReferenceCoefficientLog D L + 4))) :
    allocatedAffineSourceReferenceError B U basis S α O ρ P η M H ε mesh Cmask ≤ Real.exp (-target) := by
  let cap := Real.exp (allocatedDensityLog (G := G) B α O P) ^ Fintype.card (LayerSamplerAxis I n)
  let lip := (Fintype.card (LayerSamplerAxis I n) : ℝ) * Real.exp (allocatedDensityLog (G := G) B α O P) * cap
  let radius := max (Real.exp P * (partitionedIdealRadius α m + 1)) (Real.exp (allocatedJetSupportLog (G := G) B α O P))
  let Ki := ‖(∏ o : Outputs, |R o.1.val.1|)⁻¹‖ * ((affineProductProfileLip Outputs ρ : ℝ) * Real.exp P)
  let vol := (2 * radius) ^ Fintype.card (UnselectedColumn select) *
    (2 * radius + 2) ^ Fintype.card {o : Outputs // allocatedLongIntegerCoordinate B U basis S (O := O) o}
  have hc := affineReferenceCoefficient_bounds hD hL hdensity hsupport hP hideal hKi hCmask0 hCmask hb0 hb
    (Fintype.card (LayerSamplerAxis I n)) (Fintype.card Outputs)
    (Fintype.card (UnselectedColumn select))
    (Fintype.card {o : Outputs // allocatedLongIntegerCoordinate B U basis S (O := O) o}) ha ho hu hi
  have hc' : Cmask ^ Fintype.card (LayerSamplerAxis I n) ≤ Real.exp earlyMaskLog ∧
      Cmask ^ Fintype.card (LayerSamplerAxis I n) *
        (2 * cap * (scalarCubeGridBoundaryConstant α / volume.real (scalarCubeDomain α)) + lip * 2) *
        (2 * Real.exp (allocatedJetSupportLog (G := G) B α O P)) ^ Fintype.card Outputs ≤ Real.exp (affineReferenceCoefficientLog D L) ∧
      Cmask ^ Fintype.card (LayerSamplerAxis I n) * lip *
        (2 * Real.exp (allocatedJetSupportLog (G := G) B α O P)) ^ Fintype.card Outputs ≤ Real.exp (affineReferenceCoefficientLog D L) ∧
      Cmask ^ Fintype.card (LayerSamplerAxis I n) * vol * (Ki + lip) ≤ Real.exp (affineReferenceCoefficientLog D L) := by
    refine ⟨hearlyMask, hc.2.1, hc.2.2.1, ?_⟩
    convert hc.2.2.2 using 1
    dsimp only [vol, Ki, lip, cap, radius]
    ring
  have herr := affineReferenceError_accuracy_separated hη0 (by positivity : 0 ≤ ∑ j, (M j : ℝ) / H j)
    hε0 hmesh0 hc' hη hratio hε hmesh
  let bound : ℝ≥0 := ⟨Real.exp (allocatedDensityLog (G := G) B α O P), Real.exp_nonneg _⟩
  let capNN : ℝ≥0 := bound ^ Fintype.card (LayerSamplerAxis I n)
  let lipNN : ℝ≥0 := Fintype.card (LayerSamplerAxis I n) * bound * capNN
  let KiNN : ℝ≥0 := ‖(∏ o : Outputs, |R o.1.val.1|)⁻¹‖₊ *
    (affineProductProfileLip Outputs ρ * ⟨Real.exp P, Real.exp_nonneg _⟩)
  have hcapNN : (capNN : ℝ) = cap := rfl
  have hlipNN : (lipNN : ℝ) = lip := by
    simp only [lipNN, NNReal.coe_mul, NNReal.coe_natCast, hcapNN]
    rfl
  have hKiNN : (KiNN : ℝ) = Ki := rfl
  convert herr using 1
  change Cmask ^ Fintype.card (LayerSamplerAxis I n) *
    (η + ((2 * (capNN : ℝ) * scalarCubeGridBoundaryConstant α / volume.real (scalarCubeDomain α) + (lipNN : ℝ) * 2) *
      (∑ j, (M j : ℝ) / H j) + (lipNN : ℝ) * ε) *
      (2 * Real.exp (allocatedJetSupportLog (G := G) B α O P)) ^ Fintype.card Outputs +
      (2 * radius) ^ Fintype.card (UnselectedColumn select) *
        ((2 * radius + 2) ^ Fintype.card {o : Outputs // allocatedLongIntegerCoordinate B U basis S (O := O) o} *
          ((KiNN : ℝ) + lipNN) * mesh)) = _
  rw [hcapNN, hlipNN, hKiNN]
  dsimp only [vol]
  ring

end Erdos3.VectorPolynomial

end

end OAI
end

theorem solution.{u_1, u_2, u_3, u_4, u_5, u_6} : type_of% @OAI.Erdos3.VectorPolynomial.allocatedAffineSourceReferenceError_small_separated_s2_oai.{u_1, u_2, u_3, u_4, u_5, u_6} := @OAI.Erdos3.VectorPolynomial.allocatedAffineSourceReferenceError_small_separated_s2_oai.{u_1, u_2, u_3, u_4, u_5, u_6}
