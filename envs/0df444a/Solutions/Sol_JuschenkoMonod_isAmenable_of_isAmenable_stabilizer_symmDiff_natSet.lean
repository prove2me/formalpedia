-- Prove2me | solution 1 for JuschenkoMonod.isAmenable_of_isAmenable_stabilizer_symmDiff_natSet
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-29T21:28:37.893749+00:00
-- url     : https://prove2.me/submissions/ac2cf0fe-4987-4375-bb7d-1b003971786e

import Mathlib
import Definitions.Def_Garrido_Amenability
import Definitions.Def_IntervalExchange
import Definitions.Def_JuschenkoMonod
import Theorems.Thm_JuschenkoDeLaSalle_isAmenableAction_lamplighter_wobbling_of_isRecurrentSpace_and_isRecurrentSpace_of_coarseEmbedding_and_not_of_containsLipschitzBinaryTree
import Theorems.Thm_JuschenkoMonod_finite_symmDiff_natSet_image
import Theorems.Thm_JuschenkoMonod_isAmenable_of_isAmenableAction_of_isAmenable_stabilizer

set_option linter.unusedSectionVars false
set_option linter.deprecated false

open scoped ENNReal Pointwise

namespace JuschenkoMonod

open IntervalExchange

theorem boundedGeometry_int : HasBoundedGeometry ℤ := by
  intro R hR
  refine ⟨⌈2 * R + 1⌉₊, fun x => ⟨?_, ?_⟩⟩
  · rw [Int.closedBall_eq_Icc]; exact Set.finite_Icc _ _
  · rw [Int.closedBall_eq_Icc, ← Finset.coe_Icc, Set.ncard_coe_finset, Int.card_Icc]
    have h1 := Int.floor_le ((x : ℝ) + R)
    have h2 := Int.le_ceil ((x : ℝ) - R)
    have h3 : (⌊(x : ℝ) + R⌋ + 1 - ⌈(x : ℝ) - R⌉ : ℤ) ≤ ⌈2 * R + 1⌉₊ := by
      have h4 := Int.lt_floor_add_one ((x : ℝ) + R)
      have h5 := Int.ceil_lt_add_one ((x : ℝ) - R)
      have h6 := Nat.le_ceil (2 * R + 1)
      have : ((⌊(x : ℝ) + R⌋ + 1 - ⌈(x : ℝ) - R⌉ : ℤ) : ℝ) ≤ ((⌈2 * R + 1⌉₊ : ℕ) : ℝ) := by
        push_cast; linarith
      have : ((⌊(x : ℝ) + R⌋ + 1 - ⌈(x : ℝ) - R⌉ : ℤ) : ℝ) ≤ (((⌈2 * R + 1⌉₊ : ℕ) : ℤ) : ℝ) := by
        simpa using this
      exact_mod_cast this
    omega

theorem dist_embed_int (x y : ℤ) :
    id (dist x y) ≤ dist (![x, 0] : Fin 2 → ℤ) ![y, 0] ∧
      dist (![x, 0] : Fin 2 → ℤ) ![y, 0] ≤ id (dist x y) := by
  have : dist (![x, 0] : Fin 2 → ℤ) ![y, 0] = dist x y := by
    apply le_antisymm
    · refine (dist_pi_le_iff dist_nonneg).2 fun i => ?_
      fin_cases i <;> simp
    · simpa using dist_le_pi_dist (![x, 0] : Fin 2 → ℤ) ![y, 0] 0
  simp [this]

theorem lamp_mean_int :
    ∃ m : Set (Multiplicative (ℤ →₀ ZMod 2)) → ℝ≥0∞,
      Garrido.IsFinitelyAdditiveMeasure m ∧ m Set.univ = 1 ∧
        Garrido.IsInvariant (Lamplighter ↥(wobbling ℤ) ℤ) m := by
  have h := (JuschenkoDeLaSalle.isAmenableAction_lamplighter_wobbling_of_isRecurrentSpace_and_isRecurrentSpace_of_coarseEmbedding_and_not_of_containsLipschitzBinaryTree
    boundedGeometry_int)
  exact h.1 0 (h.2.1 (fun x => ![x, 0]) id id monotone_id monotone_id Filter.tendsto_id
    dist_embed_int 0)


abbrev Zc := Multiplicative (ℤ →₀ ZMod 2)

/-- the support of a lamp configuration, as a finite set -/
def lampSupp (f : Zc) : Finset ℤ := (Multiplicative.toAdd f).support

/-- the indicator configuration of a finite set -/
noncomputable def indicZ (F : Finset ℤ) : Zc :=
  Multiplicative.ofAdd (Finsupp.onFinset F (fun x => if x ∈ F then (1 : ZMod 2) else 0)
    (fun x hx => by by_contra h; exact hx (by simp [h])))

theorem lampSupp_indicZ (F : Finset ℤ) : lampSupp (indicZ F) = F := by
  ext x; simp [lampSupp, indicZ]

theorem lampSupp_mul (f g : Zc) : lampSupp (f * g) = symmDiff (lampSupp f) (lampSupp g) := by
  ext x
  have key : ∀ a b : ZMod 2, a + b ≠ 0 ↔ ((a ≠ 0 ∧ b = 0) ∨ (b ≠ 0 ∧ a = 0)) := by decide
  simp only [lampSupp, Finsupp.mem_support_iff, toAdd_mul, Finsupp.add_apply,
    Finset.mem_symmDiff]
  rw [key]
  tauto

theorem lampSupp_lampAut (w : ↥(wobbling ℤ)) (f : Zc) :
    lampSupp (lampAut ↥(wobbling ℤ) ℤ w f) = (lampSupp f).image (fun x => (w : Equiv.Perm ℤ) x) := by
  have hinj : Function.Injective (fun x : ℤ => w • x) := fun a b h => (MulAction.injective w) h
  unfold lampSupp
  show (Finsupp.mapDomain (fun x => w • x) (Multiplicative.toAdd f)).support = _
  rw [Finsupp.mapDomain_support_of_injective hinj]
  rfl

theorem lampSupp_smul (F : Finset ℤ) (w : ↥(wobbling ℤ)) (f : Zc) :
    lampSupp ((⟨indicZ F, w⟩ : Lamplighter ↥(wobbling ℤ) ℤ) • f) =
      symmDiff F ((lampSupp f).image (fun x => (w : Equiv.Perm ℤ) x)) := by
  show lampSupp (indicZ F * lampAut ↥(wobbling ℤ) ℤ w f) = _
  rw [lampSupp_mul, lampSupp_indicZ, lampSupp_lampAut]


theorem finite_symmDiff_aux (g : Equiv.Perm ℤ) (hg : g ∈ wobbling ℤ) :
    (symmDiff natSet (g '' natSet)).Finite :=
  finite_symmDiff_natSet_image g hg

/-- the lamp-group element `ℕ △ uℕ` -/
noncomputable def Dset (u : Equiv.Perm ℤ) (hu : u ∈ wobbling ℤ) : Finset ℤ :=
  (finite_symmDiff_aux u hu).toFinset

theorem coe_Dset (u : Equiv.Perm ℤ) (hu : u ∈ wobbling ℤ) :
    (Dset u hu : Set ℤ) = symmDiff natSet (u '' natSet) :=
  (finite_symmDiff_aux u hu).coe_toFinset

/-- `θ f = supp f △ ℕ` -/
def thetaS (f : Zc) : Set ℤ := symmDiff (lampSupp f : Set ℤ) natSet

theorem thetaS_smul (u : Equiv.Perm ℤ) (hu : u ∈ wobbling ℤ) (f : Zc) :
    thetaS ((⟨indicZ (Dset u hu), ⟨u, hu⟩⟩ : Lamplighter ↥(wobbling ℤ) ℤ) • f) =
      u '' thetaS f := by
  unfold thetaS
  rw [lampSupp_smul, Finset.coe_symmDiff, coe_Dset, Finset.coe_image,
    Set.image_symmDiff u.injective]
  ext x
  simp only [Set.mem_symmDiff, Set.mem_image]
  generalize (∃ x_1 ∈ natSet, u x_1 = x) = a
  generalize (∃ x_1 ∈ (lampSupp f : Set ℤ), u x_1 = x) = b
  generalize (x ∈ natSet) = p
  tauto

theorem prop33 (G : Subgroup (Equiv.Perm ℤ)) (hG : G ≤ wobbling ℤ)
    (h : ∀ E : Finset ℤ, Garrido.IsAmenable (MulAction.stabilizer G (symmDiff (E : Set ℤ) natSet))) :
    Garrido.IsAmenable G := by
  obtain ⟨m, hmfa, hm1, hminv⟩ := lamp_mean_int
  let Y0 : SubMulAction G (Set ℤ) :=
    { carrier := {S | ∃ E : Finset ℤ, S = symmDiff (E : Set ℤ) natSet}
      smul_mem' := by
        rintro g S ⟨E, rfl⟩
        have hg : (g : Equiv.Perm ℤ) ∈ wobbling ℤ := hG g.2
        refine ⟨symmDiff (E.image (fun x => (g : Equiv.Perm ℤ) x)) (Dset g hg), ?_⟩
        rw [Finset.coe_symmDiff, Finset.coe_image, coe_Dset]
        show (g : Equiv.Perm ℤ) '' _ = _
        rw [Set.image_symmDiff (g : Equiv.Perm ℤ).injective]
        ext x
        simp only [Set.mem_symmDiff, Set.mem_image]
        generalize (∃ x_1 ∈ natSet, (g : Equiv.Perm ℤ) x_1 = x) = a
        generalize (∃ x_1 ∈ (E : Set ℤ), (g : Equiv.Perm ℤ) x_1 = x) = b
        generalize (x ∈ natSet) = p
        tauto }
  let θ0 : Zc → Y0 := fun f => ⟨thetaS f, ⟨lampSupp f, rfl⟩⟩
  have hθ : ∀ (g : G) (f : Zc),
      g⁻¹ • θ0 f = θ0 ((⟨indicZ (Dset (g⁻¹ : G) (hG (g⁻¹ : G).2)), ⟨(g⁻¹ : G), hG (g⁻¹ : G).2⟩⟩ :
        Lamplighter ↥(wobbling ℤ) ℤ) • f) := by
    intro g f
    apply Subtype.ext
    show ((g⁻¹ : G) : Equiv.Perm ℤ) '' thetaS f = thetaS _
    rw [thetaS_smul (g⁻¹ : G) (hG (g⁻¹ : G).2) f]
  have hY : IsAmenableAction G Y0 := by
    refine ⟨fun S => m (θ0 ⁻¹' S), ⟨?_, ?_⟩, ?_, ?_⟩
    · simpa using hmfa.1
    · intro S T hST
      simp only [Set.preimage_union]
      exact hmfa.2 _ _ (hST.preimage θ0)
    · simpa using hm1
    · intro g S
      have : θ0 ⁻¹' (g • S) =
          (⟨indicZ (Dset (g⁻¹ : G) (hG (g⁻¹ : G).2)), ⟨(g⁻¹ : G), hG (g⁻¹ : G).2⟩⟩ :
            Lamplighter ↥(wobbling ℤ) ℤ)⁻¹ • (θ0 ⁻¹' S) := by
        rw [← Set.preimage_smul]
        ext f
        simp only [Set.mem_preimage, Set.mem_smul_set_iff_inv_smul_mem, ← hθ]
      simp only
      rw [this]
      exact hminv _ _
  refine isAmenable_of_isAmenableAction_of_isAmenable_stabilizer G Y0 hY fun y => ?_
  obtain ⟨E, hE⟩ := y.2
  have e : MulAction.stabilizer G y = MulAction.stabilizer G (symmDiff (E : Set ℤ) natSet) := by
    rw [SubMulAction.stabilizer_of_subMul, ← hE]
  rw [e]
  exact h E

end JuschenkoMonod

open scoped Pointwise in
theorem solution (G : Subgroup (Equiv.Perm ℤ))
    (hG : G ≤ IntervalExchange.wobbling ℤ)
    (h : ∀ E : Finset ℤ, Garrido.IsAmenable (MulAction.stabilizer G (symmDiff (E : Set ℤ) JuschenkoMonod.natSet))) :
    Garrido.IsAmenable G :=
  JuschenkoMonod.prop33 G hG h
