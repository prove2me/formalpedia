-- Prove2me | solution 1 for OAI.Elasticity.extended_dn_amplitude_transfer
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T11:00:24.87399+00:00
-- url     : https://prove2.me/submissions/9275c619-f568-4973-81df-99a7a809bfaf

import Mathlib
import Definitions.Def_ElasticityUniqueness
import Definitions.Def_OAIQ6El004
import Theorems.Thm_OAI_Elasticity_physical_classical_transfer
import Theorems.Thm_OAI_ElasticityCGO_transferred_amplitude

section
-- module Solutions.OAIQ6_Elast.Elasticity_Augmented
attribute [-instance] _root_.OAI.ElasticityGeneralSlicing.cylinder_temperate _root_.OAI.ElasticityODE.instFactLeRealOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact differential-algebra identities of the physical and normalized
augmented elasticity systems. Smooth derivatives are constructed below;
commutation and Leibniz are proved, not postulated for the physical operator. -/
noncomputable section
open scoped BigOperators
namespace ElasticityAugmented

section DifferentialAlgebra
variable {A : Type*} [CommRing A] [Algebra ℂ A]
variable {ι : Type*} [Fintype ι]
variable (D : ι → Derivation ℂ A A)

omit [Fintype ι] in
lemma partial_mul (i : ι) (a b : A) : D i (a*b) = D i a*b + a*D i b := by
  simpa only [smul_eq_mul, add_comm, mul_comm] using (D i).leibniz a b

end DifferentialAlgebra

section CovariantAlgebra
variable {A : Type*} [CommRing A] [Algebra ℂ A]
variable {ι : Type*} [Fintype ι]
variable (D : ι → Derivation ℂ A A) (T : ι → A →ₗ[ℂ] A)

variable (hD : ∀ i j f, D i (D j f) = D j (D i f))
variable (hT : ∀ i j f, T i (T j f) = T j (T i f))
variable (hTD : ∀ i a b, T i (a*b) = D i a*b+a*T i b)

omit [Fintype ι] in
lemma shifted_apply (z : ι → ℂ) (i : ι) (f : A) :
    shifted D z i f = D i f + z i • f := rfl

end CovariantAlgebra

end ElasticityAugmented

end

end OAI
end

section
-- module Solutions.OAIQ6_Elast.Elasticity_Bessel
attribute [-instance] _root_.OAI.ElasticityGeneralSlicing.cylinder_temperate _root_.OAI.ElasticityODE.instFactLeRealOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Concrete Fourier Bessel potentials for the required negative-order
supported Carleman estimate. All functions and operators are actual Schwartz
maps; no Sobolev-shift estimate is being assumed. -/
open MeasureTheory Complex SchwartzMap
open scoped BigOperators FourierTransform SchwartzMap LineDeriv ENNReal

/-! Positive commutator algebra on actual Schwartz functions, allowing
nonlocal Bessel shifts without silently retaining compact support. -/
open MeasureTheory Complex SchwartzMap LineDeriv
open scoped BigOperators LineDeriv SchwartzMap

namespace ElasticityNegativeOrder
open ElasticityBessel
open ElasticitySchwartzCarleman

section

lemma mult_apply (a : X → ℂ) (ha : a.HasTemperateGrowth) (f : S) (x : X) :
    mult a f x = a x * f x :=
  SchwartzMap.smulLeftCLM_apply_apply ha f x

end

end ElasticityNegativeOrder

end

end OAI
end

section
-- module Solutions.OAIQ6_Elast.Elasticity_Extension
attribute [-instance] _root_.OAI.ElasticityGeneralSlicing.cylinder_temperate _root_.OAI.ElasticityODE.instFactLeRealOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Filter Metric
open scoped Topology Manifold
namespace ElasticityBoundary
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

lemma compact_smooth_cutoff {K U : Set E} (hK : IsCompact K) (hU : IsOpen U) (hKU : K⊆U) :
    ∃ χ : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) χ ∧ HasCompactSupport χ ∧ tsupport χ⊆U ∧
      (∀ᶠ x in 𝓝ˢ K, χ x=1) ∧ ∀ x, χ x∈Icc 0 1 := by
  obtain ⟨R,hR⟩ := hK.isBounded.subset_ball (0 : E)
  obtain ⟨V,hV,hKV,hVU⟩ := normal_exists_closure_subset hK.isClosed (hU.inter isOpen_ball)
    (show K⊆U∩ball (0 : E) R from fun x hx => ⟨hKU hx,hR hx⟩)
  obtain ⟨χ,hχ,hzero,hb⟩ := exists_contMDiffMap_one_nhds_of_subset_interior
    (𝓘(ℝ,E)) (n := (⊤ : ℕ∞)) hK.isClosed (by rwa [hV.interior_eq])
  have hs : tsupport (χ : E → ℝ)⊆closure V := by
    apply closure_mono
    intro x hx
    by_contra hn
    exact hx (hzero x hn)
  refine ⟨χ,χ.contMDiff.contDiff,?_,fun x hx => (hVU (hs hx)).1,hχ,hb⟩
  apply (isCompact_closedBall (0 : E) R).of_isClosed_subset (isClosed_tsupport χ)
  exact fun x hx => ball_subset_closedBall ((hVU (hs hx)).2)

end ElasticityBoundary

end
end

end OAI
end

section
-- module Solutions.OAIQ6_Elast.Elasticity_Carleman
attribute [-instance] _root_.OAI.ElasticityDistribution.instIsCentralScalarSubtypeForallXComplexMemSubalgebraSmoothCoeffDist _root_.OAI.ElasticityDistribution.instIsScalarTowerComplexMulOppositeSubtypeForallXMemSubalgebraSmoothCoeffDist _root_.OAI.ElasticityDistribution.instIsScalarTowerComplexSubtypeForallXMemSubalgebraSmoothCoeffDist _root_.OAI.ElasticityDistribution.instModuleMulOppositeSubtypeForallXComplexMemSubalgebraSmoothCoeffDist _root_.OAI.ElasticityDistribution.instModuleSubtypeForallXComplexMemSubalgebraSmoothCoeffDist _root_.OAI.ElasticityDistribution.instSMulCommClassComplexSubtypeForallXMemSubalgebraSmoothCoeffDist _root_.OAI.ElasticityDistribution.instSMulMulOppositeSubtypeForallXComplexMemSubalgebraSmoothCoeffDist _root_.OAI.ElasticityDistribution.instSMulSubtypeForallXComplexMemSubalgebraSmoothCoeffDist _root_.OAI.ElasticityGeneralSlicing.cylinder_temperate _root_.OAI.ElasticityODE.instFactLeRealOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Complex SchwartzMap
open scoped BigOperators FourierTransform SchwartzMap LineDeriv ENNReal

namespace ElasticityPhysicalAlgebra
open ElasticityBessel ElasticitySchwartzCarleman ElasticityNegativeOrder

lemma toSmooth_d (f : S) (i : Fin 3) :
    toSmooth (d (e i) f) = ElasticityAugmented.coord i (toSmooth f) := by
  apply Subtype.ext
  rfl

lemma toSmooth_mult (a : Smooth) (ha : (a : X → ℂ).HasTemperateGrowth) (f : S) :
    toSmooth (mult a f) = a*toSmooth f := by
  apply Subtype.ext
  funext x
  exact mult_apply a ha f x

lemma shiftD_apply (z : Fin 3 → ℂ) (i : Fin 3) (f : S) :
    shiftD z i f = d (e i) f + z i • f := rfl

lemma toSmooth_shiftD (z : Fin 3 → ℂ) (i : Fin 3) (f : S) :
    toSmooth (shiftD z i f) = ElasticityAugmented.shifted ElasticityAugmented.coord z i (toSmooth f) := by
  simp only [shiftD_apply, map_add, map_smul, toSmooth_d, ElasticityAugmented.shifted_apply]

lemma toSmooth_physical (z : Fin 3 → ℂ) (lam m : Smooth)
    (hl : (lam : X → ℂ).HasTemperateGrowth) (hm : (m : X → ℂ).HasTemperateGrowth)
    (u : Fin 3 → S) (i : Fin 3) :
    toSmooth (physical z lam m u i) =
      ElasticityAugmented.LT (ElasticityAugmented.shifted ElasticityAugmented.coord z)
        lam m (fun j => toSmooth (u j)) i := by
  simp only [physical, ElasticityAugmented.LT, ElasticityAugmented.divT, map_add, map_sum,
    toSmooth_shiftD, toSmooth_mult lam hl, toSmooth_mult m hm,
    Finset.mul_sum, mul_add]

end ElasticityPhysicalAlgebra

open scoped BigOperators

open MeasureTheory Complex SchwartzMap
open scoped BigOperators FourierTransform SchwartzMap LineDeriv ENNReal
open Set MeasureTheory SchwartzMap
open scoped BigOperators SchwartzMap Topology

end

end OAI
end

section
-- module Solutions.OAIQ6_Elast.Elasticity_Solvability
attribute [-instance] _root_.OAI.ElasticityGeneralSlicing.cylinder_temperate _root_.OAI.ElasticityODE.instFactLeRealOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! The Hahn--Banach / Riesz step used by the physical solvability argument.
This proves the functional-analytic implication, rather than postulating
existence of a right inverse. The physical test estimate is proved separately. -/

open MeasureTheory Complex SchwartzMap
open scoped BigOperators FourierTransform SchwartzMap LineDeriv ENNReal

open MeasureTheory Complex SchwartzMap
open scoped BigOperators SchwartzMap LineDeriv
open scoped SchwartzMap LineDeriv BigOperators
open MeasureTheory Complex SchwartzMap
open scoped BigOperators SchwartzMap LineDeriv

open scoped BigOperators
namespace ElasticityCoeffBounds
open ElasticityAugmented

lemma ExteriorConstant.add {f g : Smooth} (hf : ExteriorConstant f) (hg : ExteriorConstant g) :
    ExteriorConstant (f+g) := by
  obtain ⟨c, hc⟩ := hf
  obtain ⟨d, hd⟩ := hg
  refine ⟨c+d, ?_⟩
  have he : (fun x => ((f+g : Smooth) : X → ℂ) x - (c+d)) =
      (fun x => (f : X → ℂ) x-c) + (fun x => (g : X → ℂ) x-d) := by
    funext x
    change (f : X → ℂ) x + (g : X → ℂ) x - (c+d) = _
    dsimp
    ring
  rw [he]
  exact hc.add hd

lemma reciprocal_mul (f : Smooth) (hf : ∀ x, (f : X → ℂ) x ≠ 0) :
    reciprocal f hf * f = 1 := by
  apply Subtype.ext
  funext x
  exact inv_mul_cancel₀ (hf x)

open ElasticityBessel ElasticitySchwartzCarleman ElasticityNegativeOrder
open ElasticityPhysicalAlgebra (physical phase)

end ElasticityCoeffBounds

open MeasureTheory Complex SchwartzMap
open scoped BigOperators FourierTransform SchwartzMap LineDeriv ENNReal

open MeasureTheory TemperedDistribution
open scoped ENNReal SchwartzMap BigOperators

end

end OAI
end

section
-- module Solutions.OAIQ6_Elast.Elasticity_TransportAlgebra
attribute [-instance] _root_.OAI.ElasticityDistribution.instIsCentralScalarSubtypeForallXComplexMemSubalgebraSmoothCoeffDist _root_.OAI.ElasticityDistribution.instIsScalarTowerComplexMulOppositeSubtypeForallXMemSubalgebraSmoothCoeffDist _root_.OAI.ElasticityDistribution.instIsScalarTowerComplexSubtypeForallXMemSubalgebraSmoothCoeffDist _root_.OAI.ElasticityDistribution.instModuleMulOppositeSubtypeForallXComplexMemSubalgebraSmoothCoeffDist _root_.OAI.ElasticityDistribution.instModuleSubtypeForallXComplexMemSubalgebraSmoothCoeffDist _root_.OAI.ElasticityDistribution.instSMulCommClassComplexSubtypeForallXMemSubalgebraSmoothCoeffDist _root_.OAI.ElasticityDistribution.instSMulMulOppositeSubtypeForallXComplexMemSubalgebraSmoothCoeffDist _root_.OAI.ElasticityDistribution.instSMulSubtypeForallXComplexMemSubalgebraSmoothCoeffDist _root_.OAI.ElasticityGeneralSlicing.cylinder_temperate _root_.OAI.ElasticityODE.instFactLeRealOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Filter
open scoped Topology BigOperators
namespace ElasticityAugmented

lemma localCoord_restrict {U : Set X} (hU : IsOpen U) (i : Fin 3) (f : Smooth) :
    localCoord hU i (restrictSmooth U f)=restrictSmooth U (coord i f) := by
  exact Derivation.liftOfSurjective_apply (restrictSmooth_surjective U) (restrict_coord_zero hU i) f
end ElasticityAugmented

end
end

end OAI
end

section
-- module Solutions.OAIQ6_Elast.Elasticity_CGO
attribute [-instance] _root_.OAI.ElasticityGeneralSlicing.cylinder_temperate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ElasticityAugmented
open Set
open scoped BigOperators

lemma restrict_shifted {U : Set X} (hU : IsOpen U) (z : Fin 3 → ℂ) (i : Fin 3) (f : Smooth) :
    restrictSmooth U (shifted coord z i f)=shifted (localCoord hU) z i (restrictSmooth U f) := by
  simp only [shifted_apply,map_add,map_smul,localCoord_restrict]
lemma restrict_LT {U : Set X} (hU : IsOpen U) (z : Fin 3 → ℂ) (lam m : Smooth)
    (a : Fin 3 → Smooth) (i : Fin 3) :
    restrictSmooth U (LT (shifted coord z) lam m a i)=
      LT (shifted (localCoord hU) z) (restrictSmooth U lam) (restrictSmooth U m)
        (fun j => restrictSmooth U (a j)) i := by
  simp only [LT,divT,restrict_shifted hU,map_mul,map_sum,map_add]

end ElasticityAugmented

end

end OAI
end

section
-- module Solutions.OAIQ6_Elast.Elasticity_Transfer
attribute [-instance] _root_.OAI.ElasticityGeneralSlicing.cylinder_temperate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set MeasureTheory
open scoped BigOperators SchwartzMap
namespace ElasticityCGO
open ElasticityAugmented
open ElasticityPhysicalAlgebra (toSmooth toSmooth_apply toSmooth_physical physical phase)
lemma cut_local {U : Set X} (χ : Smooth) (hc : HasCompactSupport (χ : X → ℂ))
    (hχ : EqOn (χ : X → ℂ) 1 U) (f : Smooth) :
    restrictSmooth U (toSmooth (cut χ hc f))=restrictSmooth U f := by
  apply (restrictSmooth_eq_iff U _ _).mpr
  intro x hx
  simp only [toSmooth_apply,cut_apply,hχ hx,Pi.one_apply,one_mul]
lemma physical_cut_local {U : Set X} (hU : IsOpen U)
    (z : Fin 3 → ℂ) (lam m χ : Smooth)
    (hl : (lam : X → ℂ).HasTemperateGrowth) (hm : (m : X → ℂ).HasTemperateGrowth)
    (hc : HasCompactSupport (χ : X → ℂ)) (hχ : EqOn (χ : X → ℂ) 1 U)
    (u : Fin 3 → Smooth) (i : Fin 3) :
    EqOn (physical z lam m (fun j => cut χ hc (u j)) i : X → ℂ)
      ((LT (shifted coord z) lam m u i : Smooth) : X → ℂ) U := by
  change EqOn ((toSmooth (physical z lam m (fun j => cut χ hc (u j)) i) : Smooth) : X → ℂ) _ U
  apply (restrictSmooth_eq_iff U _ _).mp
  rw [toSmooth_physical z lam m hl hm,restrict_LT hU,restrict_LT hU]
  congr 1
  funext j
  exact cut_local χ hc hχ (u j)

end ElasticityCGO

end
end
section
noncomputable section
open Set MeasureTheory
open scoped Topology BigOperators SchwartzMap
namespace ElasticityPhysicalAlgebra
open ElasticityAugmented

lemma physical_eqOn_of_eqOn {U : Set X} (hU : IsOpen U)
    (z : Fin 3 → ℂ) (lam m : Smooth)
    (hl : (lam : X → ℂ).HasTemperateGrowth) (hm : (m : X → ℂ).HasTemperateGrowth)
    (f g : Fin 3 → SchwartzMap X ℂ) (hfg : ∀ j,EqOn (f j : X → ℂ) (g j) U) (i : Fin 3) :
    EqOn (physical z lam m f i : X → ℂ) (physical z lam m g i) U := by
  change EqOn ((toSmooth (physical z lam m f i) : Smooth) : X → ℂ)
    ((toSmooth (physical z lam m g i) : Smooth) : X → ℂ) U
  apply (restrictSmooth_eq_iff U _ _).mp
  rw [toSmooth_physical z lam m hl hm,toSmooth_physical z lam m hl hm,
    restrict_LT hU,restrict_LT hU]
  congr 1
  funext j
  exact (restrictSmooth_eq_iff U _ _).mpr (hfg j)

/-- A local physical transfer that agrees off a compact set gives a genuinely
compact supported global difference, without changing the physical equation
on its open domain. -/
theorem compactify_physical_transfer {K U : Set X} (hK : IsCompact K)
    (hU : IsOpen U) (hKU : K⊆U) (lam m : Smooth)
    (hl : (lam : X → ℂ).HasTemperateGrowth) (hm : (m : X → ℂ).HasTemperateGrowth)
    (F G : Fin 3 → SchwartzMap X ℂ) (hG : ∀ i,EqOn (physical 0 lam m G i : X → ℂ) 0 U)
    (he : ∀ i,EqOn (G i : X → ℂ) (F i) (U\K)) :
    ∃ H : Fin 3 → SchwartzMap X ℂ,(∀ i,tsupport (H i)⊆K) ∧
      (∀ i,EqOn (physical 0 lam m (F+H) i : X → ℂ) 0 U) ∧
      (∀ i,EqOn ((F+H) i : X → ℂ) (G i) U) := by
  obtain ⟨χ,hχ,hc,hs,h1,_⟩ := ElasticityBoundary.compact_smooth_cutoff hK hU hKU
  let c : Smooth := ⟨fun x => (χ x : ℂ),Complex.ofRealCLM.contDiff.comp hχ⟩
  have hc' : HasCompactSupport (c : X → ℂ) := hc.comp_left Complex.ofReal_zero
  let H : Fin 3 → SchwartzMap X ℂ := fun i => ElasticityCGO.cut c hc' (toSmooth (G i-F i))
  have hH (i) (x) : H i x=(χ x : ℂ)*(G i x-F i x) := rfl
  have heq : ∀ i,EqOn ((F+H) i : X → ℂ) (G i) U := by
    intro i x hx
    change F i x+H i x=G i x
    rw [hH]
    by_cases hxK : x∈K
    · have hx1 : χ x=1 := mem_of_mem_nhds (s := {y : X | χ y=1}) (x := x) (h1.filter_mono (nhds_le_nhdsSet hxK))
      rw [hx1,Complex.ofReal_one,one_mul]
      ring
    · rw [he i ⟨hx,hxK⟩,sub_self,mul_zero,add_zero]
  refine ⟨H,?_,?_,heq⟩
  · intro i
    apply closure_minimal _ hK.isClosed
    intro x hx
    by_contra hnot
    apply hx
    rw [hH]
    by_cases hxU : x∈U
    · rw [he i ⟨hxU,hnot⟩,sub_self,mul_zero]
    · have hz : χ x=0 := image_eq_zero_of_notMem_tsupport (fun hh => hxU (hs hh))
      rw [hz,Complex.ofReal_zero,zero_mul]
  · intro i x hx
    exact (physical_eqOn_of_eqOn hU 0 lam m hl hm (F+H) G heq i hx).trans (hG i hx)
end ElasticityPhysicalAlgebra

namespace Elasticity
open ElasticityDistribution
open ElasticityPhysicalAlgebra (physical)
variable {Ω B B' : Set X} {lam₁ mu₁ lam₂ mu₂ : X → ℝ}

/-- A supported smooth physical difference derived from the actual DN equality.
This is the literal compact support needed for the augmented Carleman estimate. -/
theorem physical_supported_transfer
    (ha₁ : Admissible Ω lam₁ mu₁) (ha₂ : Admissible Ω lam₂ mu₂)
    (hΩ : IsOpen Ω) (hOB : Bornology.IsBounded Ω) (hΩB : Ω⊆B)
    (hB : IsOpen B) (hB' : IsOpen B') (hsub : B'⊆B) (hcl : closure Ω⊆B')
    (hl₁ : BoundedCoefficient B lam₁) (hm₁ : BoundedCoefficient B mu₁)
    (hl₂ : BoundedCoefficient B lam₂) (hm₂ : BoundedCoefficient B mu₂)
    (he : ∀ x∉Ω, lam₁ x=lam₂ x ∧ mu₁ x=mu₂ x)
    (hDN : DN Ω lam₁ mu₁=DN Ω lam₂ mu₂)
    (L₁ M₁ L₂ M₂ N₂ O₂ : Coeff) (hN : N₂*M₂=1) (hO : O₂*(L₂+M₂+M₂)=1)
    (hL₁ : ∀ᵐ x ∂(volume.restrict B), eval L₁ x=(lam₁ x : ℂ))
    (hM₁ : ∀ᵐ x ∂(volume.restrict B), eval M₁ x=(mu₁ x : ℂ))
    (hL₂ : ∀ᵐ x ∂(volume.restrict B), eval L₂ x=(lam₂ x : ℂ))
    (hM₂ : ∀ᵐ x ∂(volume.restrict B), eval M₂ x=(mu₂ x : ℂ))
    {g : X → ℂ} (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hc : HasCompactSupport g)
    (hs : tsupport g⊆B) (h1 : Set.EqOn g 1 B') (F : Fin 3 → SchwartzMap X ℂ)
    (hF : ∀ i, Set.EqOn (physical 0 (eval L₁) (eval M₁) F i : X → ℂ) 0 B) :
    ∃ H : Fin 3 → SchwartzMap X ℂ,(∀ i,tsupport (H i)⊆closure Ω) ∧
      (∀ i,EqOn (physical 0 (eval L₂) (eval M₂) (F+H) i : X → ℂ) 0 B') ∧
      (∀ i,EqOn ((F+H) i : X → ℂ) (F i) (closure Ω)ᶜ) := by
  obtain ⟨G,hG,heG⟩ := physical_classical_transfer ha₁ ha₂ hΩ hOB hΩB hB hB' hsub
    hl₁ hm₁ hl₂ hm₂ he hDN L₁ M₁ L₂ M₂ N₂ O₂ hN hO hL₁ hM₁ hL₂ hM₂ hg hc hs h1 F hF
  obtain ⟨H,hH,hp,_⟩ := ElasticityPhysicalAlgebra.compactify_physical_transfer
    hOB.isCompact_closure hB' hcl L₂.val M₂.val (growth L₂) (growth M₂) F G hG heG
  refine ⟨H,hH,hp,?_⟩
  intro i x hx
  have hz : H i x=0 := image_eq_zero_of_notMem_tsupport (fun hh => hx (hH i hh))
  change F i x+H i x=F i x
  rw [hz,add_zero]
end Elasticity

end
end
section
noncomputable section
open scoped BigOperators
namespace ElasticityAugmented
section Algebra
variable {A : Type*} [CommRing A] [Algebra ℂ A]
variable {ι : Type*} [Fintype ι]
variable (D : ι → Derivation ℂ A A) (z : ι → ℂ) (χ : A)
omit [Fintype ι] in
lemma deriv_phase_mul (hχ : ∀ i,D i χ=z i • χ) (i : ι) (f : A) :
    D i (χ*f)=χ*(shifted D z i f) := by
  rw [partial_mul,hχ,shifted_apply]
  simp only [Algebra.smul_def]
  ring

/-- The shifted operator is the literal exponential conjugation of the
physical stress-divergence, not a new PDE declared equivalent by hypothesis. -/
theorem physical_phase_conjugation (hχ : ∀ i,D i χ=z i • χ)
    (lam m : A) (u : ι → A) (i : ι) :
    LT (fun j => (D j).toLinearMap) lam m (fun j => χ*u j) i =
      χ*LT (shifted D z) lam m u i := by
  have hd (j) (f) := deriv_phase_mul D z χ hχ j f
  change D i (lam*(∑ j,D j (χ*u j)))+
    ∑ j,D j (m*(D j (χ*u i)+D i (χ*u j)))=_
  simp only [hd,← Finset.mul_sum,← mul_add]
  have hfirst : lam*(χ*(∑ j,shifted D z j (u j)))=χ*(lam*(∑ j,shifted D z j (u j))) := by ring
  have hsecond (j) : m*(χ*(shifted D z j (u i)+shifted D z i (u j)))=
      χ*(m*(shifted D z j (u i)+shifted D z i (u j))) := by ring
  rw [hfirst,hd]
  simp_rw [hsecond,hd]
  rw [← Finset.mul_sum,← mul_add]
  rfl
end Algebra

lemma coord_exponential (L : X →L[ℝ] ℂ) (i : Fin 3) :
    coord i (exponential L)=L (e i) • exponential L := by
  apply Subtype.ext
  funext x
  have hh := congrArg (fun K : X →L[ℝ] ℂ => K (e i)) (L.hasFDerivAt.cexp.fderiv (x := x))
  change fderiv ℝ (fun y => Complex.exp (L y)) x (e i)=L (e i)*Complex.exp (L x)
  simpa only [smul_apply,smul_eq_mul,mul_comm] using hh

theorem physical_exponential_conjugation (L : X →L[ℝ] ℂ) (lam m : Smooth)
    (u : Fin 3 → Smooth) (i : Fin 3) :
    LT (fun j => (coord j).toLinearMap) lam m (fun j => exponential L*u j) i=
      exponential L*LT (shifted coord (fun j => L (e j))) lam m u i :=
  physical_phase_conjugation coord (fun j => L (e j)) (exponential L) (coord_exponential L) lam m u i
end ElasticityAugmented

end
end
section
noncomputable section
open MeasureTheory Set
open scoped BigOperators FourierTransform

namespace ElasticityCarleman

lemma phaseCLM_e (θ : Direction) (i : Fin 3) : phaseCLM θ (e i) = θ i := by
  simp [phaseCLM, e, EuclideanSpace.proj, apply_ite]

end ElasticityCarleman

end
end
section
noncomputable section
open Set
open scoped BigOperators SchwartzMap
namespace ElasticityCGO
open ElasticityAugmented
open ElasticityPhysicalAlgebra (toSmooth toSmooth_apply toSmooth_physical physical)
open ElasticityCarleman (phaseCLM phaseCLM_e)

lemma shifted_zero : shifted coord (0 : Fin 3 → ℂ)=fun j => (coord j).toLinearMap := by
  funext j
  apply LinearMap.ext
  intro f
  change coord j f+(0 : ℂ) • f=coord j f
  rw [zero_smul,add_zero]
lemma phaseCLM_coords (z : Fin 3 → ℂ) : (fun j => phaseCLM z (e j))=z := by
  funext j
  exact phaseCLM_e z j

/-- The literal unshifted stress-divergence of a cut-off exponential field. -/
theorem expCut_physical {U : Set X} (hU : IsOpen U) (lam m χ : Smooth)
    (hl : (lam : X → ℂ).HasTemperateGrowth) (hm : (m : X → ℂ).HasTemperateGrowth)
    (hc : HasCompactSupport (χ : X → ℂ)) (hχ : EqOn (χ : X → ℂ) 1 U)
    (z : Fin 3 → ℂ) (f : Fin 3 → S) (i : Fin 3) :
    EqOn (physical 0 lam m (fun j => expCut χ hc z (f j)) i : X → ℂ)
      (fun x => Complex.exp (phaseCLM z x)*physical z lam m f i x) U := by
  intro x hx
  change physical 0 lam m (fun j => cut χ hc (exponential (phaseCLM z)*toSmooth (f j))) i x=_
  rw [physical_cut_local hU 0 lam m χ hl hm hc hχ _ i hx,shifted_zero,
    physical_exponential_conjugation,phaseCLM_coords,← toSmooth_physical z lam m hl hm f i]
  rfl

theorem expCut_solution {U : Set X} (hU : IsOpen U) (lam m χ : Smooth)
    (hl : (lam : X → ℂ).HasTemperateGrowth) (hm : (m : X → ℂ).HasTemperateGrowth)
    (hc : HasCompactSupport (χ : X → ℂ)) (hχ : EqOn (χ : X → ℂ) 1 U)
    (z : Fin 3 → ℂ) (f : Fin 3 → S)
    (hf : ∀ i,EqOn (physical z lam m f i : X → ℂ) 0 U) :
    ∀ i,EqOn (physical 0 lam m (fun j => expCut χ hc z (f j)) i : X → ℂ) 0 U := by
  intro i x hx
  rw [expCut_physical hU lam m χ hl hm hc hχ z f i hx]
  change Complex.exp (phaseCLM z x)*physical z lam m f i x=0
  rw [hf i hx]
  exact mul_zero _

end ElasticityCGO

end
end

end OAI
end

section
-- module Solutions.OAIQ6_Elast.Elasticity_CommonExterior
attribute [-instance] _root_.OAI.ElasticityGeneralSlicing.cylinder_temperate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set MeasureTheory
namespace Elasticity

lemma admissible_of_global {Ω : Set X} {l m : X → ℝ}
    (hl : ContDiff ℝ (⊤ : ℕ∞) l) (hm : ContDiff ℝ (⊤ : ℕ∞) m)
    (hp : ∀ x,0 < m x ∧ 0<3*l x+2*m x) : Admissible Ω l m :=
  ⟨⟨univ,isOpen_univ,subset_univ _,hl.contDiffOn⟩,
    ⟨univ,isOpen_univ,subset_univ _,hm.contDiffOn⟩,fun x _ => hp x⟩

end Elasticity

end
end

end OAI
end

section
-- module Solutions.OAIQ6_Elast.Elasticity_PhysicalCGO
attribute [-instance] _root_.OAI.ElasticityGeneralSlicing.cylinder_temperate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ElasticityAugmented

open Set
open scoped BigOperators
lemma real_longitudinal_positive (lam m : X → ℝ) (hp : ∀ x,0 < m x ∧ 0<3*lam x+2*m x) (x : X) :
    0<lam x+m x+m x := by have hh := hp x; linarith

end ElasticityAugmented
namespace Elasticity
open Set MeasureTheory
open scoped BigOperators SchwartzMap
open ElasticityAugmented (Smooth smoothOfReal smooth_coe)
open ElasticityCoeffBounds
open ElasticityDistribution (Coeff eval)
open ElasticityPhysicalAlgebra (physical)
open ElasticityCGO (expCut)

/-- Actual DN equality yields a shifted physical solution with a compact
amplitude difference. This uses the common-exterior coefficients from the
boundary reduction; it does not assume normalized-system transfer. The two
cutoffs are ordinary compact smooth cutoffs on nested open domains. -/
theorem extended_dn_amplitude_transfer_oai {Ω B B' : Set X}
    (hΩ : IsOpen Ω) (hOB : Bornology.IsBounded Ω) (hB : IsOpen B)
    (hBB : Bornology.IsBounded B) (hB' : IsOpen B') (hsub : B'⊆B) (hcl : closure Ω⊆B')
    (lam m : Fin 2 → X → ℝ)
    (hl : ∀ q,ContDiff ℝ (⊤ : ℕ∞) (lam q)) (hm : ∀ q,ContDiff ℝ (⊤ : ℕ∞) (m q))
    (hp : ∀ q x,0 < m q x ∧ 0<3*lam q x+2*m q x)
    (hcll : ∀ q,ExteriorConstant (smoothOfReal (lam q) (hl q)))
    (hclm : ∀ q,ExteriorConstant (smoothOfReal (m q) (hm q)))
    (he : ∀ x∉Ω,lam 0 x=lam 1 x ∧ m 0 x=m 1 x)
    (hDN : DN Ω (lam 0) (m 0)=DN Ω (lam 1) (m 1))
    (χ g : Smooth) (hcχ : HasCompactSupport (χ : X → ℂ))
    (hc : HasCompactSupport (g : X → ℂ)) (hs : tsupport (g : X → ℂ)⊆B)
    (hχ : EqOn (χ : X → ℂ) 1 B) (hg : EqOn (g : X → ℂ) 1 B')
    (z : Fin 3 → ℂ) (u : Fin 3 → SchwartzMap X ℂ)
    (hu : ∀ i,EqOn (physical z (fun x => (lam 0 x : ℂ)) (fun x => (m 0 x : ℂ)) u i : X → ℂ) 0 B) :
    ∃ v : Fin 3 → SchwartzMap X ℂ,
      (∀ i,tsupport (v i-u i : SchwartzMap X ℂ)⊆closure Ω) ∧
      (∀ i,EqOn (physical z (fun x => (lam 1 x : ℂ)) (fun x => (m 1 x : ℂ)) v i : X → ℂ) 0 B') := by
  let l := fun q => smoothOfReal (lam q) (hl q)
  let μ := fun q => smoothOfReal (m q) (hm q)
  have hn0 (x) : (μ 1 : X → ℂ) x≠0 := Complex.ofReal_ne_zero.mpr (hp 1 x).1.ne'
  have ho0 (x) : ((l 1+μ 1+μ 1 : Smooth) : X → ℂ) x≠0 := by
    change (lam 1 x : ℂ)+(m 1 x : ℂ)+(m 1 x : ℂ)≠0
    exact_mod_cast (ElasticityAugmented.real_longitudinal_positive (lam 1) (m 1) (hp 1) x).ne'
  let n := reciprocal (μ 1) hn0
  let o := reciprocal (l 1+μ 1+μ 1) ho0
  have hn : ExteriorConstant n := (hclm 1).reciprocal hn0
  have ho : ExteriorConstant o := (((hcll 1).add (hclm 1)).add (hclm 1)).reciprocal ho0
  let L : Fin 2 → Coeff := fun q => ⟨l q,(hcll q).growth⟩
  let M : Fin 2 → Coeff := fun q => ⟨μ q,(hclm q).growth⟩
  let N : Coeff := ⟨n,hn.growth⟩
  let O : Coeff := ⟨o,ho.growth⟩
  have hiN : N*M 1=1 := by apply Subtype.ext; exact reciprocal_mul (μ 1) hn0
  have hiO : O*(L 1+M 1+M 1)=1 := by apply Subtype.ext; exact reciprocal_mul (l 1+μ 1+μ 1) ho0
  have ha (q) : Admissible Ω (lam q) (m q) := admissible_of_global (hl q) (hm q) (hp q)
  have hbl (q) : BoundedCoefficient B (lam q) :=
    SmoothUpTo.boundedCoefficient ⟨univ,isOpen_univ,subset_univ _,(hl q).contDiffOn⟩ hB hBB
  have hbm (q) : BoundedCoefficient B (m q) :=
    SmoothUpTo.boundedCoefficient ⟨univ,isOpen_univ,subset_univ _,(hm q).contDiffOn⟩ hB hBB
  let F := fun i => expCut χ hcχ z (u i)
  have hF : ∀ i,EqOn (physical 0 (eval (L 0)) (eval (M 0)) F i : X → ℂ) 0 B :=
    ElasticityCGO.expCut_solution hB (l 0) (μ 0) χ (hcll 0).growth (hclm 0).growth hcχ hχ z u hu
  obtain ⟨H,hH,hsol,_⟩ := physical_supported_transfer (ha 0) (ha 1) hΩ hOB
    (subset_closure.trans (hcl.trans hsub)) hB hB' hsub hcl
    (hbl 0) (hbm 0) (hbl 1) (hbm 1) he hDN (L 0) (M 0) (L 1) (M 1) N O hiN hiO
    (Filter.Eventually.of_forall (fun _ => rfl)) (Filter.Eventually.of_forall (fun _ => rfl))
    (Filter.Eventually.of_forall (fun _ => rfl)) (Filter.Eventually.of_forall (fun _ => rfl))
    (smooth_coe g) hc hs hg F hF
  obtain ⟨v,hv,hp',_⟩ := ElasticityCGO.transferred_amplitude hB' (l 1) (μ 1) χ
    (hcll 1).growth (hclm 1).growth hcχ (hχ.mono hsub) z u F H
    (fun i x hx => by
      change expCut χ hcχ z (u i) x=_
      rw [ElasticityCGO.expCut_apply,hχ (hsub hx),Pi.one_apply,one_mul]) hH hsol
  exact ⟨v,hv,hp'⟩

open ElasticityPhysicalAlgebra (phase)
end Elasticity

end

end OAI
end

theorem solution : type_of% @OAI.Elasticity.extended_dn_amplitude_transfer_oai := @OAI.Elasticity.extended_dn_amplitude_transfer_oai
