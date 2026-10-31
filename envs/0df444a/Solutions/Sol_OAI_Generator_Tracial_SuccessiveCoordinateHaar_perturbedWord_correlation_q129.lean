-- Prove2me | solution 1 for OAI.Generator.Tracial.SuccessiveCoordinateHaar.perturbedWord_correlation_q129
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T21:35:14.571991+00:00
-- url     : https://prove2.me/submissions/ce2e4ba5-ea0a-4b6f-8a93-8d65fede69af

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ129G014
import Theorems.Thm_OAI_Generator_Tracial_SuccessiveCoordinateHaar_exponential_product_correlation_q129

section
-- module Solutions.OAIQ129_RG2.FactorGeneration_FreeWords
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.predualAlgebraDualNormed _root_.OAI.UltrapowerBridge.q129Monoid _root_.OAI.UltrapowerBridge.q129Mul _root_.OAI.UltrapowerBridge.q129MulOneClass _root_.OAI.UltrapowerBridge.q129One
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner 

namespace OAI

namespace Generator

/-! Distinct nonidentity off-diagonal prefix ratios, distinguished by abelian exponent coordinates. Labels start at zero. -/

theorem freePrefix_eq_prod (n : ℕ) :
    freePrefix n = ((List.range n).map FreeGroup.of).prod := by
  induction n with
  | zero => simp [freePrefix]
  | succ n ih => rw [freePrefix, List.prod_range_succ, ih]

/-! The exact multiplicity sum for prefix ratios, with labels g_(k+1) indexed by k : Fin n. -/

/-! Ordered prefix products. The element h denotes the unitary exponential of a self-adjoint operator, not its logarithm. The final letter is unperturbed. -/
variable {G : Type*} [Group G]

theorem conjugate_list_prod (s : G) (xs : List G) :
    (xs.map (fun g => s * g * s⁻¹)).prod = s * xs.prod * s⁻¹ := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.prod_cons]
    rw [ih]
    simp [mul_assoc]

theorem prefix_perturbation (ss : List G) (h : G) :
    ((prefixes ss).map (fun g => g * h * g⁻¹)).prod * ss.prod =
      (ss.map (fun s => s * h)).prod := by
  induction ss with
  | nil => simp [prefixes]
  | cons s ss ih =>
    have hmap : ((prefixes ss).map (fun g => (s * g) * h * (s * g)⁻¹)).prod =
        s * ((prefixes ss).map (fun g => g * h * g⁻¹)).prod * s⁻¹ := by
      rw [← conjugate_list_prod]
      simp [List.map_map, Function.comp_def, mul_assoc]
    simp only [prefixes, List.map_cons, List.map_map, Function.comp_def, List.prod_cons]
    rw [hmap]
    simpa only [mul_assoc, inv_mul_cancel_left] using congrArg (fun v => s * h * v) ih

/-- The exact prefix cancellation identity with the unperturbed terminal factor. -/
theorem prefix_perturbation_terminal (ss : List G) (h terminal : G) :
    ((prefixes ss).map (fun g => g * h * g⁻¹)).prod * (ss.prod * terminal) =
      (ss.map (fun s => s * h)).prod * terminal := by
  rw [← mul_assoc, prefix_perturbation]

end Generator

end OAI
end

section
-- module Solutions.OAIQ129_RG2.FactorGeneration_CoordinatePerturbation
attribute [-instance] _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.Generator.Tracial.projectionOrbitClosure_complete _root_.OAI.Generator.Tracial.relativeTraceSpace_complete _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner 

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Group-ring maps from actual bounded unitary coordinates, with quotient
transport and coordinate Gram limits. -/
section
open UltrapowerBridge Filter
open scoped Topology
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M) (ω : Ultrafilter ℕ)

theorem sequenceUnitaryQuotient_bounded (b : Bounded M)
    (hb : ∀ k,b.val k ∈ unitary M.toStarSubalgebra) :
    (sequenceUnitaryQuotient τ ω (boundedUnitarySequence b hb) : Q τ ω)=
      quotientMap τ (ω : Filter ℕ) b := by
  change quotientMap τ (ω : Filter ℕ) (boundedMap (boundedToSequence b))=_
  rw [boundedToSequence_map]

theorem coordinateGroupRing_single {A : Type*} (v : A → unitary (Sequences M))
    (g : FreeGroup A) : coordinateGroupRing v (MonoidAlgebra.single g 1)=(FreeGroup.lift v g : Sequences M) := by
  simp [coordinateGroupRing]

theorem freeGroup_quotient {A : Type*} (v : A → unitary (Sequences M))
    (q : A → unitary (Q τ ω)) (hv : ∀ a,sequenceUnitaryQuotient τ ω (v a)=q a)
    (g : FreeGroup A) : sequenceUnitaryQuotient τ ω (FreeGroup.lift v g)=
      unitaryRepresentation τ ω q g := by
  exact FreeGroup.lift_unique ((sequenceUnitaryQuotient τ ω).comp (FreeGroup.lift v))
    (fun a => by simpa only [MonoidHom.comp_apply,FreeGroup.lift_apply_of] using hv a)

end

/-! Prefix labels and conjugate-word Gram identities for free-group perturbations. -/
section
attribute [local instance] Classical.propDecidable Classical.decEq
open UltrapowerBridge Filter
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H} (τ : TracialRepresentation M) (ω : Ultrafilter ℕ)

set_option maxHeartbeats 1600000 in
theorem unitaryRepresentation_prefix (u : unitary (Q τ ω))
    (t : ℕ → unitary (Q τ ω)) (k : ℕ) :
    unitaryRepresentation τ ω (prefixVariable τ ω u t) (freePrefix k)=
      prefixProduct τ ω u t k := by
  induction k with
  | zero => exact map_one _
  | succ k ih =>
    rw [freePrefix,(unitaryRepresentation τ ω (prefixVariable τ ω u t)).map_mul,ih]
    change prefixProduct τ ω u t k*FreeGroup.lift (prefixVariable τ ω u t) (FreeGroup.of k)=_
    rw [FreeGroup.lift_apply_of]
    rfl

end

/-! The literal bounded coordinate model of the finite-prefix free group.
The t_j sequences are the witnesses retained by the successive construction. -/
section
attribute [local instance] Classical.propDecidable Classical.decEq
open UltrapowerBridge Filter
open scoped Topology
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H} (τ : TracialRepresentation M) (ω : Ultrafilter ℕ)

variable {hNM : N ≤ M} {seed : Set (Q τ ω)}

theorem SuccessiveCoordinateHaar.haarSequence_quotient (F : SuccessiveCoordinateHaar τ ω hNM seed)
    (j : ℕ) : sequenceUnitaryQuotient τ ω (F.haarSequence τ ω j)=(F.step j).t := by
  apply Subtype.ext
  exact (sequenceUnitaryQuotient_bounded τ ω
    (boundedInclusion hNM (F.step j).coordinates)
    (fun k => Unitary.map_mem (coordinateInclusion hNM) ((F.step j).unitary_coordinates k))).trans
      (F.step j).represents

theorem SuccessiveCoordinateHaar.coordinateVariables_quotient
    (F : SuccessiveCoordinateHaar τ ω hNM seed) (u : unitary M.toStarSubalgebra) (j : ℕ) :
    sequenceUnitaryQuotient τ ω (F.coordinateVariables τ ω u j)=
      prefixVariable τ ω (constantQuotientUnitary τ ω u) (fun k => (F.step k).t) j := by
  cases j with
  | zero => exact F.haarSequence_quotient τ ω 0
  | succ j =>
    change sequenceUnitaryQuotient τ ω (constantSequenceUnitary u*F.haarSequence τ ω (j+1))=_
    rw [(sequenceUnitaryQuotient τ ω).map_mul,F.haarSequence_quotient]
    rfl

end

/-! The one literal bounded skew-adjoint perturbation K = i h. Every formal
row is its conjugate by the corresponding actual coordinate prefix. -/
attribute [local instance] Classical.propDecidable Classical.decEq
open UltrapowerBridge
open scoped BigOperators
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H} (τ : TracialRepresentation M) (ω : Ultrafilter ℕ)
variable {hNM : N ≤ M} {seed : Set (Q τ ω)}

theorem SuccessiveCoordinateHaar.coordinateLabels_pair
    (F : SuccessiveCoordinateHaar τ ω hNM seed)
    (u : unitary M.toStarSubalgebra) {ell : ℕ} (k j : Fin ell) :
    F.coordinateLabels τ ω u ell (pairLabel k j)=
      F.coordinatePrefix τ ω u (k.val+1)*(F.coordinatePrefix τ ω u (j.val+1))⁻¹ := by
  change FreeGroup.lift _ (freePrefix _*(freePrefix _)⁻¹)=_
  rw [(FreeGroup.lift (F.coordinateVariables τ ω u)).map_mul,
    (FreeGroup.lift (F.coordinateVariables τ ω u)).map_inv]
  rfl

theorem SuccessiveCoordinateHaar.perturbationMap_row
    (F : SuccessiveCoordinateHaar τ ω hNM seed)
    (u z : unitary M.toStarSubalgebra) {ell : ℕ} (α : ℝ) (k : Fin ell) :
    F.perturbationMap τ ω u z ell (finitePerturbationRow α k)=
      (F.coordinatePrefix τ ω u (k.val+1) : Sequences M)*
        F.commonPerturbation τ ω u z ell α*
        star (F.coordinatePrefix τ ω u (k.val+1) : Sequences M) := by
  let Φ := F.perturbationMap τ ω u z ell
  have hs (r : ℝ) (a : MonoidAlgebra ℂ (FreeGroup (PrefixLabel ell))) : Φ (r • a)=r • Φ a :=
    map_smul (Φ.restrictScalars ℝ).toLinearMap r a
  have hgen (p : PrefixLabel ell) : Φ (MonoidAlgebra.single (FreeGroup.of p) 1)=
      (F.coordinateConjugates τ ω u z ell p : Sequences M) := by
    change coordinateGroupRing _ _=_
    rw [coordinateGroupRing_single,FreeGroup.lift_apply_of]
  have hinv (p : PrefixLabel ell) : Φ (MonoidAlgebra.single ((FreeGroup.of p)⁻¹) 1)=
      star (F.coordinateConjugates τ ω u z ell p : Sequences M) := by
    change coordinateGroupRing _ _=_
    rw [coordinateGroupRing_single,map_inv,FreeGroup.lift_apply_of]
    rfl
  change Φ (finitePerturbationRow α k)=_
  rw [finitePerturbationRow,hs,commonPerturbation]
  simp only [map_sum,map_sub,hgen,hinv,mul_smul_comm,smul_mul_assoc,
    Finset.mul_sum,Finset.sum_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [coordinateConjugates,coordinateLabels_pair]
  simp only [← Unitary.star_eq_inv,Submonoid.coe_mul,Unitary.coe_star]
  simp only [star_mul,star_star,mul_sub,sub_mul,mul_assoc]

theorem sequence_exp_conjugate (g : unitary (Sequences M)) (a : Sequences M) :
    NormedSpace.exp ((g : Sequences M)*a*star (g : Sequences M))=
      (g : Sequences M)*NormedSpace.exp a*star (g : Sequences M) := by
  have h : SemiconjBy (g : Sequences M) a ((g : Sequences M)*a*star (g : Sequences M)) := by
    unfold SemiconjBy
    simp only [mul_assoc,Unitary.coe_star_mul_self,mul_one]
  have he := congrArg (fun b : Sequences M => b*star (g : Sequences M)) h.exp_right
  have hg : (g : Sequences M)*star (g : Sequences M)=1 := g.property.2
  simpa only [mul_assoc,hg,mul_one] using he.symm

theorem SuccessiveCoordinateHaar.exponential_row
    (F : SuccessiveCoordinateHaar τ ω hNM seed)
    (u z : unitary M.toStarSubalgebra) {ell : ℕ} (α : ℝ) (k : Fin ell) :
    NormedSpace.exp (F.perturbationMap τ ω u z ell (finitePerturbationRow α k))=
      (↑(F.coordinatePrefix τ ω u (k.val+1)*F.perturbingUnitary τ ω u z ell α*
        (F.coordinatePrefix τ ω u (k.val+1))⁻¹) : Sequences M) := by
  rw [F.perturbationMap_row,sequence_exp_conjugate]
  rfl

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ129_RG2.FactorGeneration_WordCorrelation
attribute [-instance] _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.Generator.Tracial.relativeTraceSpace_complete _root_.OAI.Generator.predualAlgebraDualNormed
attribute [-simp] _root_.OAI.Generator.Tracial.cyclicCoefficient_apply _root_.OAI.Generator.Tracial.cyclicPredualEvaluation_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner 

namespace OAI

noncomputable section

namespace Generator

/-! Ordered prefix cancellation for the actual common perturbed unitary.
All identities are identities of bounded coordinate sequences. -/
section
variable {G : Type*} [Group G]

theorem prefixes_append_single (xs : List G) (x : G) :
    prefixes (xs++[x])=prefixes xs++[xs.prod*x] := by
  induction xs with
  | nil => simp [prefixes]
  | cons a xs ih => simp [prefixes,ih,List.map_append,mul_assoc]

theorem evaluated_prefixes (s : ℕ → G) (n : ℕ) :
    prefixes ((List.range n).map s)=
      (List.range n).map (fun k => FreeGroup.lift s (freePrefix (k+1))) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.range_succ,List.map_append,List.map_singleton,prefixes_append_single,ih,
      List.map_append,List.map_singleton]
    congr 2
    rw [freePrefix,map_mul,FreeGroup.lift_apply_of,freePrefix_eq_prod,map_list_prod]
    simp only [List.map_map,Function.comp_def,FreeGroup.lift_apply_of]

/-- The terminal letter is unperturbed; the same h occurs before every u. -/
theorem interleaved_terminal (t : ℕ → G) (u h : G) (n : ℕ) :
    let s : ℕ → G := fun k => if k=0 then t 0 else u*t k
    ((List.range n).map (fun k => s k*h)).prod*s n=
      t 0*((List.range n).map (fun k => h*u*t (k+1))).prod := by
  dsimp only
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.prod_range_succ,List.prod_range_succ]
    simp only [Nat.add_one_ne_zero,ite_false, if_false]
    calc
      _ = (((List.range n).map (fun k => (if k=0 then t 0 else u*t k)*h)).prod*
          (if n=0 then t 0 else u*t n))*(h*u*t (n+1)) := by simp only [mul_assoc]
      _ = _ := by rw [ih]; simp only [mul_assoc]

end
namespace Tracial

section
attribute [local instance] Classical.propDecidable Classical.decEq
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H} (τ : TracialRepresentation M) (ω : Ultrafilter ℕ)
variable {hNM : N ≤ M} {seed : Set (Q τ ω)}

theorem SuccessiveCoordinateHaar.coordinatePrefix_terminal
    (F : SuccessiveCoordinateHaar τ ω hNM seed)
    (u : unitary M.toStarSubalgebra) (ell : ℕ) :
    F.coordinatePrefix τ ω u (ell+1)=
      ((List.range ell).map (F.coordinateVariables τ ω u)).prod*
        F.coordinateVariables τ ω u ell := by
  rw [coordinatePrefix,freePrefix,(FreeGroup.lift (F.coordinateVariables τ ω u)).map_mul,
    FreeGroup.lift_apply_of,
    freePrefix_eq_prod,map_list_prod]
  simp only [List.map_map,Function.comp_def,FreeGroup.lift_apply_of]

theorem SuccessiveCoordinateHaar.perturbedWord_prefixes
    (F : SuccessiveCoordinateHaar τ ω hNM seed)
    (u z : unitary M.toStarSubalgebra) (ell : ℕ) (α : ℝ) :
    ((List.range ell).map (fun k => F.coordinatePrefix τ ω u (k+1)*
      F.perturbingUnitary τ ω u z ell α*(F.coordinatePrefix τ ω u (k+1))⁻¹)).prod*
      F.coordinatePrefix τ ω u (ell+1)=F.perturbedWord τ ω u z ell α := by
  rw [F.coordinatePrefix_terminal]
  have hp := prefix_perturbation_terminal ((List.range ell).map (F.coordinateVariables τ ω u))
    (F.perturbingUnitary τ ω u z ell α) (F.coordinateVariables τ ω u ell)
  rw [evaluated_prefixes,List.map_map] at hp
  rw [show ((List.range ell).map (fun k => F.coordinatePrefix τ ω u (k+1)*
      F.perturbingUnitary τ ω u z ell α*(F.coordinatePrefix τ ω u (k+1))⁻¹)).prod*
      (((List.range ell).map (F.coordinateVariables τ ω u)).prod*F.coordinateVariables τ ω u ell)=
      (((List.range ell).map (F.coordinateVariables τ ω u)).map
        (fun s => s*F.perturbingUnitary τ ω u z ell α)).prod*F.coordinateVariables τ ω u ell from hp]
  have hs : F.coordinateVariables τ ω u = fun k =>
      if k=0 then F.haarSequence τ ω 0 else constantSequenceUnitary u*F.haarSequence τ ω k := by
    funext k
    cases k <;> simp [coordinateVariables]
  rw [List.map_map,hs]
  exact interleaved_terminal _ _ _ ell

theorem SuccessiveCoordinateHaar.exponential_product_eq_word
    (F : SuccessiveCoordinateHaar τ ω hNM seed)
    (u z : unitary M.toStarSubalgebra) (ell : ℕ) (α : ℝ) :
    ((finitePerturbationRows ell α).map
      (fun r => NormedSpace.exp (F.perturbationMap τ ω u z ell r))).prod*
      (F.coordinatePrefix τ ω u (ell+1) : Sequences M)=
        (F.perturbedWord τ ω u z ell α : Sequences M) := by
  have hr := congrArg (fun a : unitary (Sequences M) => (a : Sequences M))
    (F.perturbedWord_prefixes τ ω u z ell α)
  rw [finitePerturbationRows,List.map_ofFn]
  simp only [Function.comp_def,F.exponential_row]
  rw [List.ofFn_eq_map]
  change ((List.finRange ell).map ((fun k : ℕ => (↑(F.coordinatePrefix τ ω u (k+1)*
    F.perturbingUnitary τ ω u z ell α*(F.coordinatePrefix τ ω u (k+1))⁻¹) : Sequences M)) ∘ Fin.val)).prod * _ = _
  rw [← List.map_map,show (List.finRange ell).map Fin.val=List.range ell from by ext i; simp]
  simpa only [Submonoid.coe_mul,Submonoid.coe_list_prod,List.map_map,Function.comp_def] using hr

end

/-! The exact first-order trace calculation for the manuscript's prefix labels. -/

/-! The first-order term is exactly the sum of the mapped formal rows, and
its correlation is the manuscript's alpha/2 coefficient. -/

/-! The uniform trace correlation for the actual product of coordinate
exponentials. Identifying that product with a single-unitary perturbation word
is a separate remaining step. -/

/-! The uniform correlation now belongs to the literal word in one common
perturbed unitary, as required by eq:perturbation-prefix. -/
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H} (τ : TracialRepresentation M) (ω : Ultrafilter ℕ)
variable {hNM : N ≤ M} {seed : Set (Q τ ω)}

theorem SuccessiveCoordinateHaar.coordinatePrefix_quotient
    (F : SuccessiveCoordinateHaar τ ω hNM seed) (u : unitary M.toStarSubalgebra) (k : ℕ) :
    sequenceUnitaryQuotient τ ω (F.coordinatePrefix τ ω u k)=
      prefixProduct τ ω (constantQuotientUnitary τ ω u) (fun j => (F.step j).t) k := by
  rw [coordinatePrefix,freeGroup_quotient τ ω _ _ (F.coordinateVariables_quotient τ ω u),
    unitaryRepresentation_prefix]

theorem SuccessiveCoordinateHaar.perturbedWord_correlation_q129_oai
    (F : SuccessiveCoordinateHaar τ ω hNM seed) (u z : unitary M.toStarSubalgebra)
    (xi : Q τ ω)
    (hu : (constantQuotientUnitary τ ω u : Q τ ω) ∈ seed)
    (hz : (constantQuotientUnitary τ ω z : Q τ ω) ∈ seed) (hxi : xi ∈ seed)
    (ell : ℕ) (hell : 0 < ell) (α : ℝ) (hα : 0 < α) (hhalf : α < 1/2) :
    ‖quotientTrace τ ω (star xi*sequenceQuotient τ ω
        (F.perturbedWord τ ω u z ell α : Sequences M))-
      (α : ℂ)/2*quotientTrace τ ω (star xi*(constantQuotientUnitary τ ω z : Q τ ω))‖ ≤
        ‖xi‖*(4*α^2/(1-2*α)) := by
  rw [← F.exponential_product_eq_word,map_mul]
  have hp := congrArg Subtype.val (F.coordinatePrefix_quotient τ ω u (ell+1))
  change sequenceQuotient τ ω (F.coordinatePrefix τ ω u (ell+1) : Sequences M)=_ at hp
  rw [hp]
  exact F.exponential_product_correlation_q129 τ ω u z xi hu hz hxi ell hell α hα hhalf

end Tracial

end Generator

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.Generator.Tracial.SuccessiveCoordinateHaar.perturbedWord_correlation_q129_oai.{u_1} := @OAI.Generator.Tracial.SuccessiveCoordinateHaar.perturbedWord_correlation_q129_oai.{u_1}
