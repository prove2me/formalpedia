-- Prove2me | solution 1 for HopfAlgebra.exists_hopfAlgebra_withConv_equiv_of_isOpen_stabilizer
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/1ae61e38-e357-5d5e-bb3d-c6004f335451

import Mathlib.FieldTheory.KrullTopology
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Bialgebra.Convolution
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Algebra.Algebra.Pi
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HopfAlgebra_exists_hopfAlgebra_withConv_equiv_of_isOpen_stabilizer

set_option autoImplicit false

namespace GaloisPoints

variable (F L : Type) [Field F] [Field L] [Algebra F L]

private def eqvFun (X : Type) [MulAction (L ≃ₐ[F] L) X] : Subalgebra F (X → L) where
  carrier := {f | ∀ (σ : L ≃ₐ[F] L) (x : X), f (σ • x) = σ (f x)}
  mul_mem' := by
    intro f g hf hg σ x
    simp only [Pi.mul_apply, map_mul, hf σ x, hg σ x]
  add_mem' := by
    intro f g hf hg σ x
    simp only [Pi.add_apply, map_add, hf σ x, hg σ x]
  algebraMap_mem' := by
    intro c σ x
    simp only [Pi.algebraMap_apply, AlgEquiv.commutes]

variable {F L}

private theorem mem_eqvFun_iff {X : Type} [MulAction (L ≃ₐ[F] L) X] (f : X → L) :
    f ∈ eqvFun F L X ↔ ∀ (σ : L ≃ₐ[F] L) (x : X), f (σ • x) = σ (f x) := Iff.rfl

variable (F L)

private def evalPt {X : Type} [MulAction (L ≃ₐ[F] L) X] (x : X) : eqvFun F L X →ₐ[F] L :=
  (Pi.evalAlgHom F (fun _ : X => L) x).comp (eqvFun F L X).val

@[scoped simp] private theorem evalPt_apply {X : Type} [MulAction (L ≃ₐ[F] L) X] (x : X) (f : eqvFun F L X) :
    evalPt F L x f = (f : X → L) x := rfl

private theorem evalPt_smul {X : Type} [MulAction (L ≃ₐ[F] L) X] (σ : L ≃ₐ[F] L) (x : X) :
    evalPt F L (σ • x) = (σ : L →ₐ[F] L).comp (evalPt F L x) := by
  ext f; exact f.2 σ x

private def pull {X Y : Type} [MulAction (L ≃ₐ[F] L) X] [MulAction (L ≃ₐ[F] L) Y]
    (φ : X → Y) (hφ : ∀ (σ : L ≃ₐ[F] L) (x : X), φ (σ • x) = σ • φ x) :
    eqvFun F L Y →ₐ[F] eqvFun F L X where
  toFun f := ⟨fun x => (f : Y → L) (φ x), fun σ x => by
    show (f : Y → L) (φ (σ • x)) = σ ((f : Y → L) (φ x)); rw [hφ]; exact f.2 σ (φ x)⟩
  map_one' := by ext; rfl
  map_mul' _ _ := by ext; rfl
  map_zero' := by ext; rfl
  map_add' _ _ := by ext; rfl
  commutes' _ := by ext; rfl

@[scoped simp] private theorem coe_pull_apply {X Y : Type} [MulAction (L ≃ₐ[F] L) X] [MulAction (L ≃ₐ[F] L) Y]
    (φ : X → Y) (hφ : ∀ (σ : L ≃ₐ[F] L) (x : X), φ (σ • x) = σ • φ x) (f : eqvFun F L Y) (x : X) :
    (pull F L φ hφ f : X → L) x = (f : Y → L) (φ x) := rfl

open scoped TensorProduct

private noncomputable def prodMap (X Y : Type) [MulAction (L ≃ₐ[F] L) X] [MulAction (L ≃ₐ[F] L) Y] :
    eqvFun F L X ⊗[F] eqvFun F L Y →ₐ[F] eqvFun F L (X × Y) :=
  Algebra.TensorProduct.lift
    (pull F L (Prod.fst : X × Y → X) (fun _ _ => rfl))
    (pull F L (Prod.snd : X × Y → Y) (fun _ _ => rfl))
    (fun _ _ => Commute.all _ _)

@[scoped simp] private theorem coe_prodMap_tmul {X Y : Type} [MulAction (L ≃ₐ[F] L) X] [MulAction (L ≃ₐ[F] L) Y]
    (f : eqvFun F L X) (g : eqvFun F L Y) (z : X × Y) :
    (prodMap F L X Y (f ⊗ₜ g) : X × Y → L) z = (f : X → L) z.1 * (g : Y → L) z.2 := by
  simp [prodMap, Algebra.TensorProduct.lift_tmul]

section orbitExtend

variable {X : Type} [MulAction (L ≃ₐ[F] L) X]

open scoped Classical in

private noncomputable def orbitExtendFun (x₀ : X) (a : L) : X → L := fun y =>
  if h : y ∈ MulAction.orbit (L ≃ₐ[F] L) x₀ then (Classical.choose (MulAction.mem_orbit_iff.mp h)) a
  else 0

private theorem orbitExtendFun_smul (x₀ : X) (a : L) (ha : ∀ σ : L ≃ₐ[F] L, σ • x₀ = x₀ → σ a = a)
    (σ : L ≃ₐ[F] L) : orbitExtendFun F L x₀ a (σ • x₀) = σ a := by
  have hmem : σ • x₀ ∈ MulAction.orbit (L ≃ₐ[F] L) x₀ := MulAction.mem_orbit x₀ σ
  have hspec := Classical.choose_spec (MulAction.mem_orbit_iff.mp hmem)
  unfold orbitExtendFun
  rw [dif_pos hmem]
  have h1 : (σ⁻¹ * Classical.choose (MulAction.mem_orbit_iff.mp hmem)) • x₀ = x₀ := by
    rw [mul_smul, hspec, inv_smul_smul]
  have h2 := ha _ h1
  rw [AlgEquiv.mul_apply, AlgEquiv.aut_inv] at h2
  calc (Classical.choose (MulAction.mem_orbit_iff.mp hmem)) a
      = σ (σ.symm ((Classical.choose (MulAction.mem_orbit_iff.mp hmem)) a)) :=
        (σ.apply_symm_apply _).symm
    _ = σ a := by rw [h2]

private theorem orbitExtendFun_self (x₀ : X) (a : L) (ha : ∀ σ : L ≃ₐ[F] L, σ • x₀ = x₀ → σ a = a) :
    orbitExtendFun F L x₀ a x₀ = a := by
  have h := orbitExtendFun_smul F L x₀ a ha 1
  rwa [one_smul, AlgEquiv.one_apply] at h

private theorem orbitExtendFun_of_notMem (x₀ : X) (a : L) {y : X}
    (hy : y ∉ MulAction.orbit (L ≃ₐ[F] L) x₀) : orbitExtendFun F L x₀ a y = 0 := by
  unfold orbitExtendFun
  rw [dif_neg hy]

private theorem smul_notMem_orbit (x₀ : X) {y : X} (hy : y ∉ MulAction.orbit (L ≃ₐ[F] L) x₀)
    (τ : L ≃ₐ[F] L) : τ • y ∉ MulAction.orbit (L ≃ₐ[F] L) x₀ := by
  intro h
  obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp h
  exact hy (MulAction.mem_orbit_iff.mpr ⟨τ⁻¹ * g, by rw [mul_smul, hg, inv_smul_smul]⟩)

private theorem orbitExtendFun_mem (x₀ : X) (a : L) (ha : ∀ σ : L ≃ₐ[F] L, σ • x₀ = x₀ → σ a = a) :
    orbitExtendFun F L x₀ a ∈ eqvFun F L X := by
  rw [mem_eqvFun_iff]
  intro τ y
  by_cases hy : y ∈ MulAction.orbit (L ≃ₐ[F] L) x₀
  · obtain ⟨g, rfl⟩ := MulAction.mem_orbit_iff.mp hy
    rw [← mul_smul, orbitExtendFun_smul F L x₀ a ha, orbitExtendFun_smul F L x₀ a ha,
      AlgEquiv.mul_apply]
  · rw [orbitExtendFun_of_notMem F L x₀ a (smul_notMem_orbit F L x₀ hy τ),
      orbitExtendFun_of_notMem F L x₀ a hy, map_zero]

private noncomputable def orbitExtend (x₀ : X) (a : L) (ha : ∀ σ : L ≃ₐ[F] L, σ • x₀ = x₀ → σ a = a) :
    eqvFun F L X :=
  ⟨orbitExtendFun F L x₀ a, orbitExtendFun_mem F L x₀ a ha⟩

@[scoped simp] private theorem coe_orbitExtend (x₀ : X) (a : L) (ha : ∀ σ : L ≃ₐ[F] L, σ • x₀ = x₀ → σ a = a) :
    (orbitExtend F L x₀ a ha : X → L) = orbitExtendFun F L x₀ a := rfl

private theorem orbitExtendFun_one_mul_self (x₀ : X) :
    orbitExtendFun F L x₀ 1 * orbitExtendFun F L x₀ 1 = orbitExtendFun F L x₀ 1 := by
  funext y
  rw [Pi.mul_apply]
  by_cases hy : y ∈ MulAction.orbit (L ≃ₐ[F] L) x₀
  · obtain ⟨g, rfl⟩ := MulAction.mem_orbit_iff.mp hy
    rw [orbitExtendFun_smul F L x₀ 1 (fun σ _ => map_one σ), map_one, mul_one]
  · rw [orbitExtendFun_of_notMem F L x₀ 1 hy, mul_zero]

private theorem orbitExtendFun_mul (x₀ : X) (a b : L) (ha : ∀ σ : L ≃ₐ[F] L, σ • x₀ = x₀ → σ a = a)
    (hb : ∀ σ : L ≃ₐ[F] L, σ • x₀ = x₀ → σ b = b) :
    orbitExtendFun F L x₀ (a * b) = orbitExtendFun F L x₀ a * orbitExtendFun F L x₀ b := by
  funext y
  rw [Pi.mul_apply]
  by_cases hy : y ∈ MulAction.orbit (L ≃ₐ[F] L) x₀
  · obtain ⟨g, rfl⟩ := MulAction.mem_orbit_iff.mp hy
    rw [orbitExtendFun_smul F L x₀ a ha, orbitExtendFun_smul F L x₀ b hb,
      orbitExtendFun_smul F L x₀ (a * b) (fun σ hσ => by rw [map_mul, ha σ hσ, hb σ hσ]), map_mul]
  · simp only [orbitExtendFun_of_notMem F L _ _ hy, mul_zero]

private theorem orbitExtendFun_add (x₀ : X) (a b : L) (ha : ∀ σ : L ≃ₐ[F] L, σ • x₀ = x₀ → σ a = a)
    (hb : ∀ σ : L ≃ₐ[F] L, σ • x₀ = x₀ → σ b = b) :
    orbitExtendFun F L x₀ (a + b) = orbitExtendFun F L x₀ a + orbitExtendFun F L x₀ b := by
  funext y
  rw [Pi.add_apply]
  by_cases hy : y ∈ MulAction.orbit (L ≃ₐ[F] L) x₀
  · obtain ⟨g, rfl⟩ := MulAction.mem_orbit_iff.mp hy
    rw [orbitExtendFun_smul F L x₀ a ha, orbitExtendFun_smul F L x₀ b hb,
      orbitExtendFun_smul F L x₀ (a + b) (fun σ hσ => by rw [map_add, ha σ hσ, hb σ hσ]), map_add]
  · simp only [orbitExtendFun_of_notMem F L _ _ hy, add_zero]

private theorem orbitExtendFun_zero (x₀ : X) : orbitExtendFun F L x₀ (0 : L) = 0 := by
  funext y
  rw [Pi.zero_apply]
  by_cases hy : y ∈ MulAction.orbit (L ≃ₐ[F] L) x₀
  · obtain ⟨g, rfl⟩ := MulAction.mem_orbit_iff.mp hy
    rw [orbitExtendFun_smul F L x₀ 0 (fun σ _ => map_zero σ), map_zero]
  · exact orbitExtendFun_of_notMem F L x₀ 0 hy

private theorem orbitExtendFun_algebraMap (x₀ : X) (c : F) :
    orbitExtendFun F L x₀ (algebraMap F L c) = c • orbitExtendFun F L x₀ 1 := by
  funext y
  rw [Pi.smul_apply]
  by_cases hy : y ∈ MulAction.orbit (L ≃ₐ[F] L) x₀
  · obtain ⟨g, rfl⟩ := MulAction.mem_orbit_iff.mp hy
    rw [orbitExtendFun_smul F L x₀ _ (fun σ _ => σ.commutes c), orbitExtendFun_smul F L x₀ 1
      (fun σ _ => map_one σ), g.commutes c, map_one, Algebra.algebraMap_eq_smul_one]
  · simp only [orbitExtendFun_of_notMem F L _ _ hy, smul_zero]

private theorem mul_orbitExtendFun_one (x₀ : X) (f : eqvFun F L X) :
    (f : X → L) * orbitExtendFun F L x₀ 1 = orbitExtendFun F L x₀ ((f : X → L) x₀) := by
  funext y
  rw [Pi.mul_apply]
  by_cases hy : y ∈ MulAction.orbit (L ≃ₐ[F] L) x₀
  · obtain ⟨g, rfl⟩ := MulAction.mem_orbit_iff.mp hy
    rw [orbitExtendFun_smul F L x₀ 1 (fun σ _ => map_one σ), map_one, mul_one,
      orbitExtendFun_smul F L x₀ _ (fun σ hσ => by rw [← f.2 σ x₀, hσ]), f.2 g x₀]
  · simp only [orbitExtendFun_of_notMem F L _ _ hy, mul_zero]

private theorem sum_orbitExtend_one [Finite X] :
    letI : Fintype (MulAction.orbitRel.Quotient (L ≃ₐ[F] L) X) := Fintype.ofFinite _
    (1 : eqvFun F L X) = ∑ q : MulAction.orbitRel.Quotient (L ≃ₐ[F] L) X,
      orbitExtend F L q.out 1 (fun σ _ => map_one σ) := by
  classical
  letI : Fintype (MulAction.orbitRel.Quotient (L ≃ₐ[F] L) X) := Fintype.ofFinite _
  apply Subtype.ext
  funext y
  rw [AddSubmonoidClass.coe_finsetSum, Finset.sum_apply]
  have hterm : ∀ q : MulAction.orbitRel.Quotient (L ≃ₐ[F] L) X,
      (orbitExtend F L q.out 1 (fun σ _ => map_one σ) : X → L) y =
        if (Quotient.mk'' y : MulAction.orbitRel.Quotient (L ≃ₐ[F] L) X) = q then 1 else 0 := by
    intro q
    have horb : MulAction.orbit (L ≃ₐ[F] L) q.out = q.orbit :=
      (MulAction.orbitRel.Quotient.orbit_eq_orbit_out q Quotient.out_eq').symm
    rw [coe_orbitExtend]
    by_cases hy : y ∈ MulAction.orbit (L ≃ₐ[F] L) q.out
    · have hq : (Quotient.mk'' y : MulAction.orbitRel.Quotient (L ≃ₐ[F] L) X) = q :=
        MulAction.orbitRel.Quotient.mem_orbit.mp (horb ▸ hy)
      obtain ⟨g, rfl⟩ := MulAction.mem_orbit_iff.mp hy
      rw [orbitExtendFun_smul F L _ 1 (fun σ _ => map_one σ), map_one, if_pos hq]
    · have hq : ¬ (Quotient.mk'' y : MulAction.orbitRel.Quotient (L ≃ₐ[F] L) X) = q := fun h =>
        hy (horb ▸ MulAction.orbitRel.Quotient.mem_orbit.mpr h)
      rw [orbitExtendFun_of_notMem F L _ 1 hy, if_neg hq]
  simp only [hterm, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rfl

end orbitExtend

private theorem stabilizer_prod_isOpen {X Y : Type} [MulAction (L ≃ₐ[F] L) X] [MulAction (L ≃ₐ[F] L) Y]
    (hX : ∀ x : X, IsOpen (MulAction.stabilizer (L ≃ₐ[F] L) x : Set (L ≃ₐ[F] L)))
    (hY : ∀ y : Y, IsOpen (MulAction.stabilizer (L ≃ₐ[F] L) y : Set (L ≃ₐ[F] L))) (z : X × Y) :
    IsOpen (MulAction.stabilizer (L ≃ₐ[F] L) z : Set (L ≃ₐ[F] L)) := by
  obtain ⟨x, y⟩ := z
  have h : (MulAction.stabilizer (L ≃ₐ[F] L) (x, y) : Set (L ≃ₐ[F] L)) =
      (MulAction.stabilizer (L ≃ₐ[F] L) x : Set (L ≃ₐ[F] L)) ∩
        (MulAction.stabilizer (L ≃ₐ[F] L) y : Set (L ≃ₐ[F] L)) := by
    ext σ
    simp only [SetLike.mem_coe, MulAction.mem_stabilizer_iff, Set.mem_inter_iff, Prod.smul_mk,
      Prod.mk.injEq]
  rw [h]
  exact (hX x).inter (hY y)

section descent
variable [IsGalois F L]

section artin

private theorem artin {X : Type} [MulAction (L ≃ₐ[F] L) X] {ι : Type} {f : ι → eqvFun F L X}
    (hf : LinearIndependent F f) (s : Finset ι) :
    ∀ c : ι → L, (∀ x : X, ∑ i ∈ s, c i * (f i : X → L) x = 0) → ∀ i ∈ s, c i = 0 := by
  classical
  induction s using Finset.strongInduction with
  | H s ih =>
  intro c hc
  by_contra! hne
  obtain ⟨i₀, hi₀, hc₀⟩ := hne

  obtain ⟨c', hc'⟩ : ∃ c' : ι → L, c' = fun i => (c i₀)⁻¹ * c i := ⟨_, rfl⟩
  have hc'₀ : c' i₀ = 1 := by
    simp only [hc']
    exact inv_mul_cancel₀ hc₀
  have hrel : ∀ x : X, ∑ i ∈ s, c' i * (f i : X → L) x = 0 := by
    intro x
    have : ∑ i ∈ s, c' i * (f i : X → L) x = (c i₀)⁻¹ * ∑ i ∈ s, c i * (f i : X → L) x := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by simp only [hc', mul_assoc]
    rw [this, hc x, mul_zero]

  have hfix : ∀ (τ : L ≃ₐ[F] L), ∀ i ∈ s, τ (c' i) = c' i := by
    intro τ
    have hτrel : ∀ x : X, ∑ i ∈ s, τ (c' i) * (f i : X → L) x = 0 := by
      intro x
      have h1 := hrel (τ.symm • x)
      have h2 : ∑ i ∈ s, c' i * (f i : X → L) (τ.symm • x) =
          ∑ i ∈ s, c' i * τ.symm ((f i : X → L) x) :=
        Finset.sum_congr rfl fun i _ => by rw [(f i).2 τ.symm x]
      rw [h2] at h1
      have h3 := congrArg τ h1
      rw [map_sum, map_zero] at h3
      rw [← h3]
      exact Finset.sum_congr rfl fun i _ => by
        rw [map_mul τ (c' i) (τ.symm ((f i : X → L) x)), τ.apply_symm_apply]

    have hdiff : ∀ x : X, ∑ i ∈ s.erase i₀, (c' i - τ (c' i)) * (f i : X → L) x = 0 := by
      intro x
      rw [Finset.sum_erase s (by rw [hc'₀, map_one, sub_self, zero_mul])]
      simp only [sub_mul, Finset.sum_sub_distrib, hrel x, hτrel x, sub_self]
    have hz := ih (s.erase i₀) (Finset.erase_ssubset hi₀) _ hdiff
    intro i hi
    by_cases hii : i = i₀
    · subst hii; rw [hc'₀, map_one]
    · exact (sub_eq_zero.mp (hz i (Finset.mem_erase.mpr ⟨hii, hi⟩))).symm

  have hex : ∀ i : ι, ∃ b : F, i ∈ s → algebraMap F L b = c' i := by
    intro i
    by_cases hi : i ∈ s
    · obtain ⟨b, hb⟩ := (InfiniteGalois.mem_range_algebraMap_iff_fixed (c' i)).mpr
        (fun τ => hfix τ i hi)
      exact ⟨b, fun _ => hb⟩
    · exact ⟨0, fun h => (hi h).elim⟩
  choose b hb using hex

  have hsum : ∑ i ∈ s, b i • f i = 0 := by
    apply Subtype.ext
    funext x
    rw [AddSubmonoidClass.coe_finsetSum, Finset.sum_apply, ZeroMemClass.coe_zero, Pi.zero_apply,
      ← hrel x]
    exact Finset.sum_congr rfl fun i hi => by
      rw [SetLike.val_smul, Pi.smul_apply, Algebra.smul_def, hb i hi]
  have hb₀ : b i₀ = 0 := linearIndependent_iff'.mp hf s b hsum i₀ hi₀
  have : c' i₀ = 0 := by rw [← hb i₀ hi₀, hb₀, map_zero]
  rw [hc'₀] at this
  exact one_ne_zero this

end artin

private theorem evalPt_bijective (X : Type) [MulAction (L ≃ₐ[F] L) X] [Finite X]
    (hX : ∀ x : X, IsOpen (MulAction.stabilizer (L ≃ₐ[F] L) x : Set (L ≃ₐ[F] L))) :
    Function.Bijective (evalPt F L : X → (eqvFun F L X →ₐ[F] L)) := by
  classical
  refine ⟨fun x x' hxx' => ?_, fun φ => ?_⟩
  ·
    have hval : ∀ f : eqvFun F L X, (f : X → L) x = (f : X → L) x' := fun f => by
      have h := congrArg (fun ψ : eqvFun F L X →ₐ[F] L => ψ f) hxx'
      simpa only [evalPt_apply] using h
    by_contra hne
    by_cases hx' : x' ∈ MulAction.orbit (L ≃ₐ[F] L) x
    ·

      obtain ⟨τ, rfl⟩ := MulAction.mem_orbit_iff.mp hx'
      have hτ : τ ∉ MulAction.stabilizer (L ≃ₐ[F] L) x := fun h =>
        hne (MulAction.mem_stabilizer_iff.mp h).symm
      let H : ClosedSubgroup (L ≃ₐ[F] L) :=
        ⟨MulAction.stabilizer (L ≃ₐ[F] L) x, Subgroup.isClosed_of_isOpen _ (hX x)⟩
      have hcorr := InfiniteGalois.fixingSubgroup_fixedField H
      have hτ' : τ ∉ (IntermediateField.fixedField (H : Subgroup (L ≃ₐ[F] L))).fixingSubgroup := by
        rw [hcorr]; exact hτ
      rw [IntermediateField.mem_fixingSubgroup_iff] at hτ'
      simp only [not_forall] at hτ'
      obtain ⟨a, ha, hτa⟩ := hτ'
      have ha' : ∀ σ : L ≃ₐ[F] L, σ • x = x → σ a = a := fun σ hσ =>
        (IntermediateField.mem_fixedField_iff _ _).mp ha σ (MulAction.mem_stabilizer_iff.mpr hσ)
      have h := hval (orbitExtend F L x a ha')
      rw [coe_orbitExtend, orbitExtendFun_self F L x a ha', orbitExtendFun_smul F L x a ha'] at h
      exact hτa h.symm
    ·
      have h := hval (orbitExtend F L x 1 (fun σ _ => map_one σ))
      rw [coe_orbitExtend, orbitExtendFun_self F L x 1 (fun σ _ => map_one σ),
        orbitExtendFun_of_notMem F L x 1 hx'] at h
      exact one_ne_zero h
  ·
    letI : Fintype (MulAction.orbitRel.Quotient (L ≃ₐ[F] L) X) := Fintype.ofFinite _
    obtain ⟨x₀, hx₀⟩ : ∃ x₀ : X, φ (orbitExtend F L x₀ 1 (fun σ _ => map_one σ)) ≠ 0 := by
      by_contra! hall
      have h := congrArg φ (sum_orbitExtend_one F L (X := X))
      rw [map_one, map_sum] at h
      simp only [hall, Finset.sum_const_zero] at h
      exact one_ne_zero h
    set e₀ : eqvFun F L X := orbitExtend F L x₀ 1 (fun σ _ => map_one σ) with he₀
    have he₀sq : e₀ * e₀ = e₀ :=
      Subtype.ext (by rw [MulMemClass.coe_mul, he₀, coe_orbitExtend]; exact
        orbitExtendFun_one_mul_self F L x₀)
    have hφe : φ e₀ = 1 := by
      have h := congrArg φ he₀sq
      rw [map_mul] at h
      exact mul_left_cancel₀ hx₀ (by rw [h, mul_one])

    set K : IntermediateField F L :=
      IntermediateField.fixedField (MulAction.stabilizer (L ≃ₐ[F] L) x₀) with hK
    have hKfix : ∀ a : K, ∀ σ : L ≃ₐ[F] L, σ • x₀ = x₀ → σ (a : L) = a := fun a σ hσ =>
      (IntermediateField.mem_fixedField_iff _ _).mp a.2 σ (MulAction.mem_stabilizer_iff.mpr hσ)
    let ψ : K →ₐ[F] L :=
      { toFun := fun a => φ (orbitExtend F L x₀ a (hKfix a))
        map_one' := by
          have h1 : orbitExtend F L x₀ ((1 : K) : L) (hKfix 1) = e₀ :=
            Subtype.ext (congrArg (orbitExtendFun F L x₀) (OneMemClass.coe_one K))
          show φ (orbitExtend F L x₀ ((1 : K) : L) (hKfix 1)) = 1
          rw [h1, hφe]
        map_mul' := fun a b => by
          show φ (orbitExtend F L x₀ ((a * b : K) : L) (hKfix (a * b))) =
            φ (orbitExtend F L x₀ a (hKfix a)) * φ (orbitExtend F L x₀ b (hKfix b))
          rw [← map_mul]
          congr 1
          apply Subtype.ext
          simp only [coe_orbitExtend, MulMemClass.coe_mul]
          exact orbitExtendFun_mul F L x₀ a b (hKfix a) (hKfix b)
        map_zero' := by
          show φ (orbitExtend F L x₀ ((0 : K) : L) (hKfix 0)) = 0
          have h0 : orbitExtend F L x₀ ((0 : K) : L) (hKfix 0) = 0 := by
            apply Subtype.ext
            show orbitExtendFun F L x₀ (0 : L) = (0 : X → L)
            exact orbitExtendFun_zero F L x₀
          rw [h0, map_zero]
        map_add' := fun a b => by
          show φ (orbitExtend F L x₀ ((a + b : K) : L) (hKfix (a + b))) =
            φ (orbitExtend F L x₀ a (hKfix a)) + φ (orbitExtend F L x₀ b (hKfix b))
          rw [← map_add]
          congr 1
          apply Subtype.ext
          simp only [coe_orbitExtend, AddMemClass.coe_add]
          exact orbitExtendFun_add F L x₀ a b (hKfix a) (hKfix b)
        commutes' := fun c => by
          show φ (orbitExtend F L x₀ ((algebraMap F K c : K) : L) (hKfix _)) = algebraMap F L c
          have h1 : orbitExtend F L x₀ ((algebraMap F K c : K) : L) (hKfix _) = c • e₀ := by
            apply Subtype.ext
            show orbitExtendFun F L x₀ (algebraMap F L c) = c • orbitExtendFun F L x₀ 1
            exact orbitExtendFun_algebraMap F L x₀ c
          rw [h1, map_smul, hφe, Algebra.algebraMap_eq_smul_one] }

    let θ : L →ₐ[F] L := ψ.liftNormal L
    have hθ : ∀ a : K, θ (a : L) = ψ a := fun a => by
      have h := AlgHom.liftNormal_commutes ψ L a
      rwa [IntermediateField.algebraMap_apply, Algebra.algebraMap_self_apply] at h
    let σ : L ≃ₐ[F] L := AlgEquiv.ofBijective θ (Algebra.IsAlgebraic.algHom_bijective θ)
    refine ⟨σ • x₀, ?_⟩
    ext f
    rw [evalPt_apply, f.2 σ x₀]
    have hfx : (f : X → L) x₀ ∈ K :=
      (IntermediateField.mem_fixedField_iff _ _).mpr fun τ hτ => by
        rw [← f.2 τ x₀, MulAction.mem_stabilizer_iff.mp hτ]
    have hfe : f * e₀ = orbitExtend F L x₀ ((f : X → L) x₀) (hKfix ⟨_, hfx⟩) :=
      Subtype.ext (by rw [MulMemClass.coe_mul, he₀, coe_orbitExtend, coe_orbitExtend]; exact
        mul_orbitExtendFun_one F L x₀ f)
    calc σ ((f : X → L) x₀) = θ (((⟨_, hfx⟩ : K) : K) : L) := rfl
      _ = ψ ⟨_, hfx⟩ := hθ _
      _ = φ (orbitExtend F L x₀ ((f : X → L) x₀) (hKfix ⟨_, hfx⟩)) := rfl
      _ = φ (f * e₀) := by rw [hfe]
      _ = φ f := by rw [map_mul, hφe, mul_one]

private theorem eqvFun_finite (X : Type) [MulAction (L ≃ₐ[F] L) X] [Finite X]
    (hX : ∀ x : X, IsOpen (MulAction.stabilizer (L ≃ₐ[F] L) x : Set (L ≃ₐ[F] L))) :
    Module.Finite F (eqvFun F L X) := by

  have hK : ∀ x : X, ∃ K : IntermediateField F L, FiniteDimensional F K ∧
      (K.fixingSubgroup : Set (L ≃ₐ[F] L)) ⊆
        (MulAction.stabilizer (L ≃ₐ[F] L) x : Set (L ≃ₐ[F] L)) :=
    fun x => (krullTopology_mem_nhds_one_iff F L _).mp ((hX x).mem_nhds (Subgroup.one_mem _))
  choose K hKfin hKle using hK

  have hval : ∀ (f : eqvFun F L X) (x : X), (f : X → L) x ∈ K x := by
    intro f x
    rw [← InfiniteGalois.fixedField_fixingSubgroup (K x), IntermediateField.mem_fixedField_iff]
    intro σ hσ
    have hmem : σ ∈ MulAction.stabilizer (L ≃ₐ[F] L) x := hKle x hσ
    have hσx : σ • x = x := MulAction.mem_stabilizer_iff.mp hmem
    have hf : (f : X → L) (σ • x) = σ ((f : X → L) x) := f.2 σ x
    rw [← hf, hσx]

  let Φ : eqvFun F L X →ₗ[F] (∀ x : X, K x) :=
    { toFun := fun f x => ⟨(f : X → L) x, hval f x⟩
      map_add' := fun f g => by funext x; rfl
      map_smul' := fun c f => by funext x; rfl }
  have hΦ : Function.Injective Φ := by
    intro f g hfg
    apply Subtype.ext
    funext x
    exact congrArg (fun h : ∀ x : X, K x => ((h x : K x) : L)) hfg
  haveI : ∀ x : X, FiniteDimensional F (K x) := hKfin
  exact FiniteDimensional.of_injective Φ hΦ

section counting

private theorem exists_eq_sum_tmul {A B : Type} [AddCommGroup A] [Module F A] [AddCommGroup B] [Module F B]
    {n : ℕ} (b : Module.Basis (Fin n) F A) (t : A ⊗[F] B) : ∃ g : Fin n → B, t = ∑ i, b i ⊗ₜ[F] g i := by
  induction t using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | tmul a c =>
    refine ⟨fun i => b.repr a i • c, ?_⟩
    conv_lhs => rw [← b.sum_repr a]
    rw [TensorProduct.sum_tmul]
    exact Finset.sum_congr rfl fun i _ => TensorProduct.smul_tmul _ _ _
  | add t₁ t₂ h₁ h₂ =>
    obtain ⟨g₁, rfl⟩ := h₁
    obtain ⟨g₂, rfl⟩ := h₂
    exact ⟨g₁ + g₂, by simp only [Pi.add_apply, TensorProduct.tmul_add, Finset.sum_add_distrib]⟩

private theorem card_le_finrank (X : Type) [MulAction (L ≃ₐ[F] L) X] [Finite X]
    (hX : ∀ x : X, IsOpen (MulAction.stabilizer (L ≃ₐ[F] L) x : Set (L ≃ₐ[F] L))) :
    Nat.card X ≤ Module.finrank F (eqvFun F L X) := by
  classical
  haveI := eqvFun_finite F L X hX
  letI : Fintype X := Fintype.ofFinite X
  have hinj : Function.Injective (evalPt F L : X → (eqvFun F L X →ₐ[F] L)) :=
    (evalPt_bijective F L X hX).1

  have h1 : LinearIndependent L (fun x : X => ((evalPt F L x : eqvFun F L X →* L) :
      eqvFun F L X → L)) :=
    (linearIndependent_monoidHom (eqvFun F L X) L).comp
      (fun x : X => (evalPt F L x : eqvFun F L X →* L)) (fun x y hxy => hinj (by
        ext f
        exact congrArg (fun g : eqvFun F L X →* L => g f) hxy))
  let toFun : (eqvFun F L X →ₗ[F] L) →ₗ[L] (eqvFun F L X → L) :=
    { toFun := fun g => ⇑g
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hv : LinearIndependent L (fun x : X => (evalPt F L x).toLinearMap) :=
    LinearIndependent.of_comp toFun h1

  let e : (Fin (Module.finrank F (eqvFun F L X)) → L) ≃ₗ[L] (eqvFun F L X →ₗ[F] L) :=
    (Module.finBasis F (eqvFun F L X)).constr L
  haveI : Module.Finite L (eqvFun F L X →ₗ[F] L) := Module.Finite.equiv e
  have hfr : Module.finrank L (eqvFun F L X →ₗ[F] L) = Module.finrank F (eqvFun F L X) := by
    rw [← e.finrank_eq, Module.finrank_fin_fun]
  have h := hv.fintype_card_le_finrank
  rw [hfr] at h
  rwa [Nat.card_eq_fintype_card]

private theorem finrank_le_card (X : Type) [MulAction (L ≃ₐ[F] L) X] [Finite X]
    (hX : ∀ x : X, IsOpen (MulAction.stabilizer (L ≃ₐ[F] L) x : Set (L ≃ₐ[F] L))) :
    Module.finrank F (eqvFun F L X) ≤ Nat.card X := by
  classical
  haveI := eqvFun_finite F L X hX
  letI : Fintype X := Fintype.ofFinite X
  set b := Module.finBasis F (eqvFun F L X) with hb
  have hind : LinearIndependent L (fun i => (b i : X → L)) := by
    rw [linearIndependent_iff']
    intro s c hs i hi
    refine artin F L b.linearIndependent s c (fun x => ?_) i hi
    have h := congrFun hs x
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] using h
  have h := hind.fintype_card_le_finrank
  rw [Fintype.card_fin, Module.finrank_fintype_fun_eq_card] at h
  rwa [Nat.card_eq_fintype_card]

private theorem finrank_eqvFun (X : Type) [MulAction (L ≃ₐ[F] L) X] [Finite X]
    (hX : ∀ x : X, IsOpen (MulAction.stabilizer (L ≃ₐ[F] L) x : Set (L ≃ₐ[F] L))) :
    Module.finrank F (eqvFun F L X) = Nat.card X :=
  le_antisymm (finrank_le_card F L X hX) (card_le_finrank F L X hX)

end counting

private theorem prodMap_injective (X Y : Type) [MulAction (L ≃ₐ[F] L) X] [MulAction (L ≃ₐ[F] L) Y] [Finite X]
    (hX : ∀ x : X, IsOpen (MulAction.stabilizer (L ≃ₐ[F] L) x : Set (L ≃ₐ[F] L))) :
    Function.Injective (prodMap F L X Y) := by
  classical
  haveI hA := eqvFun_finite F L X hX
  set b := Module.finBasis F (eqvFun F L X) with hb
  rw [injective_iff_map_eq_zero]
  intro t ht
  obtain ⟨g, rfl⟩ := exists_eq_sum_tmul F b t
  have hg : ∀ i, g i = 0 := by
    intro i
    apply Subtype.ext
    funext y
    have key : ∀ x : X, ∑ j ∈ Finset.univ, (g j : Y → L) y * (b j : X → L) x = 0 := by
      intro x
      have h := congrFun (congrArg (fun u : eqvFun F L (X × Y) => (u : X × Y → L)) ht) (x, y)
      simp only [map_sum, AddSubmonoidClass.coe_finsetSum, Finset.sum_apply, coe_prodMap_tmul,
        ZeroMemClass.coe_zero, Pi.zero_apply] at h
      rw [← h]
      exact Finset.sum_congr rfl fun j _ => mul_comm _ _
    exact artin F L b.linearIndependent Finset.univ _ key i (Finset.mem_univ i)
  simp only [hg, TensorProduct.tmul_zero, Finset.sum_const_zero]

private theorem surjective_of_injective_of_finrank_mul_eq {A B C : Type} [AddCommGroup A] [Module F A]
    [AddCommGroup B] [Module F B] [AddCommGroup C] [Module F C]
    (hA : Module.Finite F A) (hB : Module.Finite F B) (hC : Module.Finite F C)
    (g : A ⊗[F] B →ₗ[F] C) (hinj : Function.Injective g)
    (h : Module.finrank F A * Module.finrank F B = Module.finrank F C) : Function.Surjective g := by
  haveI := hA
  haveI := hB
  haveI := hC
  have hdim : Module.finrank F (A ⊗[F] B) = Module.finrank F C := by
    rw [Module.finrank_tensorProduct, h]
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hinj

private theorem prodMap_bijective (X Y : Type) [MulAction (L ≃ₐ[F] L) X] [MulAction (L ≃ₐ[F] L) Y]
    [Finite X] [Finite Y]
    (hX : ∀ x : X, IsOpen (MulAction.stabilizer (L ≃ₐ[F] L) x : Set (L ≃ₐ[F] L)))
    (hY : ∀ y : Y, IsOpen (MulAction.stabilizer (L ≃ₐ[F] L) y : Set (L ≃ₐ[F] L))) :
    Function.Bijective (prodMap F L X Y) := by
  have hXY := stabilizer_prod_isOpen F L hX hY
  have hinj := prodMap_injective F L X Y hX
  have h : Module.finrank F (eqvFun F L X) * Module.finrank F (eqvFun F L Y) =
      Module.finrank F (eqvFun F L (X × Y)) := by
    rw [finrank_eqvFun F L X hX, finrank_eqvFun F L Y hY, finrank_eqvFun F L (X × Y) hXY,
      Nat.card_prod]
  exact ⟨hinj, surjective_of_injective_of_finrank_mul_eq F (eqvFun_finite F L X hX)
    (eqvFun_finite F L Y hY) (eqvFun_finite F L (X × Y) hXY) (prodMap F L X Y).toLinearMap hinj h⟩

private theorem exists_algebraMap_eq_of_forall_smul_eq (a : L) (ha : ∀ σ : L ≃ₐ[F] L, σ a = a) :
    ∃ c : F, algebraMap F L c = a := by

  obtain ⟨c, hc⟩ := (InfiniteGalois.mem_range_algebraMap_iff_fixed a).mpr ha
  exact ⟨c, hc⟩

end descent

private def Carrier (X : Type) [MulAction (L ≃ₐ[F] L) X] : Type := ↥(eqvFun F L X)

private noncomputable scoped instance instCommRingCarrier (X : Type) [MulAction (L ≃ₐ[F] L) X] :
    CommRing (Carrier F L X) := inferInstanceAs (CommRing ↥(eqvFun F L X))

private noncomputable scoped instance instAlgebraCarrier (X : Type) [MulAction (L ≃ₐ[F] L) X] :
    Algebra F (Carrier F L X) := inferInstanceAs (Algebra F ↥(eqvFun F L X))

private scoped instance instCoeFunCarrier (X : Type) [MulAction (L ≃ₐ[F] L) X] :
    CoeFun (Carrier F L X) (fun _ => X → L) := ⟨fun f => Subtype.val f⟩

variable {F L} in
private theorem Carrier.ext {X : Type} [MulAction (L ≃ₐ[F] L) X] {f g : Carrier F L X}
    (h : (f : X → L) = g) : f = g := Subtype.ext h

variable {F L} in
private theorem Carrier.eqv {X : Type} [MulAction (L ≃ₐ[F] L) X] (f : Carrier F L X) (σ : L ≃ₐ[F] L) (x : X) :
    f (σ • x) = σ (f x) := (show ↥(eqvFun F L X) from f).2 σ x

@[scoped simp] private theorem Carrier.zero_apply {X : Type} [MulAction (L ≃ₐ[F] L) X] (x : X) :
    (0 : Carrier F L X) x = 0 := rfl

p2m_reactivate "P2MW.S_HopfAlgebra_exists_hopfAlgebra_withConv_equiv_of_isOpen_stabilizer.GaloisPoints.Carrier"
@[scoped simp] private theorem Carrier.one_apply {X : Type} [MulAction (L ≃ₐ[F] L) X] (x : X) :
    (1 : Carrier F L X) x = 1 := rfl

p2m_reactivate "P2MW.S_HopfAlgebra_exists_hopfAlgebra_withConv_equiv_of_isOpen_stabilizer.GaloisPoints.Carrier"
@[scoped simp] private theorem Carrier.mul_apply {X : Type} [MulAction (L ≃ₐ[F] L) X] (f g : Carrier F L X) (x : X) :
    (f * g) x = f x * g x := rfl

p2m_reactivate "P2MW.S_HopfAlgebra_exists_hopfAlgebra_withConv_equiv_of_isOpen_stabilizer.GaloisPoints.Carrier"
@[scoped simp] private theorem Carrier.add_apply {X : Type} [MulAction (L ≃ₐ[F] L) X] (f g : Carrier F L X) (x : X) :
    (f + g) x = f x + g x := rfl

p2m_reactivate "P2MW.S_HopfAlgebra_exists_hopfAlgebra_withConv_equiv_of_isOpen_stabilizer.GaloisPoints.Carrier"
@[scoped simp] private theorem Carrier.algebraMap_apply {X : Type} [MulAction (L ≃ₐ[F] L) X] (c : F) (x : X) :
    (algebraMap F (Carrier F L X) c) x = algebraMap F L c := rfl

p2m_reactivate "P2MW.S_HopfAlgebra_exists_hopfAlgebra_withConv_equiv_of_isOpen_stabilizer.GaloisPoints.Carrier"
@[scoped simp] private theorem Carrier.smul_apply {X : Type} [MulAction (L ≃ₐ[F] L) X] (c : F) (f : Carrier F L X) (x : X) :
    (c • f) x = c • f x := rfl

p2m_reactivate "P2MW.S_HopfAlgebra_exists_hopfAlgebra_withConv_equiv_of_isOpen_stabilizer.GaloisPoints.Carrier"
section hopf

private def ev {X : Type} [MulAction (L ≃ₐ[F] L) X] (x : X) : Carrier F L X →ₐ[F] L := evalPt F L x

@[scoped simp] private theorem ev_apply {X : Type} [MulAction (L ≃ₐ[F] L) X] (x : X) (f : Carrier F L X) :
    ev F L x f = (f : X → L) x := rfl

private theorem ev_smul {X : Type} [MulAction (L ≃ₐ[F] L) X] (σ : L ≃ₐ[F] L) (x : X) :
    ev F L (σ • x) = (σ : L →ₐ[F] L).comp (ev F L x) := evalPt_smul F L σ x

private noncomputable def pm (X Y : Type) [MulAction (L ≃ₐ[F] L) X] [MulAction (L ≃ₐ[F] L) Y] :
    Carrier F L X ⊗[F] Carrier F L Y →ₐ[F] Carrier F L (X × Y) := prodMap F L X Y

@[scoped simp] private theorem coe_pm_tmul {X Y : Type} [MulAction (L ≃ₐ[F] L) X] [MulAction (L ≃ₐ[F] L) Y]
    (f : Carrier F L X) (g : Carrier F L Y) (z : X × Y) :
    (pm F L X Y (f ⊗ₜ g) : X × Y → L) z = (f : X → L) z.1 * (g : Y → L) z.2 := coe_prodMap_tmul F L f g z

private theorem pm_bijective [IsGalois F L] (X Y : Type) [MulAction (L ≃ₐ[F] L) X] [MulAction (L ≃ₐ[F] L) Y]
    [Finite X] [Finite Y]
    (hX : ∀ x : X, IsOpen (MulAction.stabilizer (L ≃ₐ[F] L) x : Set (L ≃ₐ[F] L)))
    (hY : ∀ y : Y, IsOpen (MulAction.stabilizer (L ≃ₐ[F] L) y : Set (L ≃ₐ[F] L))) :
    Function.Bijective (pm F L X Y) := prodMap_bijective F L X Y hX hY

variable [IsGalois F L]
variable (N : Type) [AddCommGroup N] [DistribMulAction (L ≃ₐ[F] L) N]

omit [IsGalois F L] in

private theorem isOpen_stabilizer_prod {X Y : Type} [MulAction (L ≃ₐ[F] L) X] [MulAction (L ≃ₐ[F] L) Y]
    (hX : ∀ x : X, IsOpen (MulAction.stabilizer (L ≃ₐ[F] L) x : Set (L ≃ₐ[F] L)))
    (hY : ∀ y : Y, IsOpen (MulAction.stabilizer (L ≃ₐ[F] L) y : Set (L ≃ₐ[F] L))) (z : X × Y) :
    IsOpen (MulAction.stabilizer (L ≃ₐ[F] L) z : Set (L ≃ₐ[F] L)) := by
  have h : (MulAction.stabilizer (L ≃ₐ[F] L) z : Set (L ≃ₐ[F] L)) =
      (MulAction.stabilizer (L ≃ₐ[F] L) z.1 : Set (L ≃ₐ[F] L)) ∩
        (MulAction.stabilizer (L ≃ₐ[F] L) z.2 : Set (L ≃ₐ[F] L)) := by
    ext σ
    simp only [SetLike.mem_coe, MulAction.mem_stabilizer_iff, Set.mem_inter_iff, Prod.ext_iff,
      Prod.smul_fst, Prod.smul_snd]
  rw [h]; exact (hX z.1).inter (hY z.2)

private def addPull : Carrier F L N →ₐ[F] Carrier F L (N × N) :=
  pull F L (fun z : N × N => z.1 + z.2) (fun σ z => by simp [smul_add])

private def negPull : Carrier F L N →ₐ[F] Carrier F L N :=
  pull F L (fun x : N => -x) (fun σ x => by simp [smul_neg])

private noncomputable def chi (x y : N) : Carrier F L N ⊗[F] Carrier F L N →ₐ[F] L :=
  Algebra.TensorProduct.lift (ev F L x) (ev F L y) (fun _ _ => Commute.all _ _)

omit [IsGalois F L] in
@[scoped simp] private theorem chi_tmul (x y : N) (f g : Carrier F L N) :
    chi F L N x y (f ⊗ₜ g) = (f : N → L) x * (g : N → L) y := by
  simp [chi, Algebra.TensorProduct.lift_tmul]

omit [IsGalois F L] in
private theorem chi_eq_ev_comp_pm (x y : N) :
    chi F L N x y = (ev F L (x, y)).comp (pm F L N N) := by
  apply Algebra.TensorProduct.ext'
  intro f g
  simp [chi_tmul, coe_pm_tmul]

private theorem ext_of_chi (hN : ∀ x : N, IsOpen (MulAction.stabilizer (L ≃ₐ[F] L) x : Set (L ≃ₐ[F] L)))
    [Finite N] {t₁ t₂ : Carrier F L N ⊗[F] Carrier F L N}
    (h : ∀ x y : N, chi F L N x y t₁ = chi F L N x y t₂) : t₁ = t₂ := by
  apply (pm_bijective F L N N hN hN).1
  apply Subtype.ext; funext z
  have := h z.1 z.2
  simpa [chi_eq_ev_comp_pm] using this

variable {N} in
private theorem counit_aux (f : Carrier F L N) : ∃ c : F, algebraMap F L c = (f : N → L) 0 := by
  apply exists_algebraMap_eq_of_forall_smul_eq F L
  intro σ
  have h := f.2 σ (0 : N)
  rw [smul_zero] at h
  exact h.symm

private noncomputable def counitFun (f : Carrier F L N) : F := Classical.choose (counit_aux F L f)

private theorem algebraMap_counitFun (f : Carrier F L N) :
    algebraMap F L (counitFun F L N f) = (f : N → L) 0 :=
  Classical.choose_spec (counit_aux F L f)

private noncomputable def counitAlg : Carrier F L N →ₐ[F] F where
  toFun := counitFun F L N
  map_one' := (algebraMap F L).injective (by rw [algebraMap_counitFun, map_one]; rfl)
  map_mul' f g := (algebraMap F L).injective (by
    rw [algebraMap_counitFun, map_mul, algebraMap_counitFun, algebraMap_counitFun]; rfl)
  map_zero' := (algebraMap F L).injective (by rw [algebraMap_counitFun, map_zero]; rfl)
  map_add' f g := (algebraMap F L).injective (by
    rw [algebraMap_counitFun, map_add, algebraMap_counitFun, algebraMap_counitFun]; rfl)
  commutes' c := (algebraMap F L).injective (by
    rw [algebraMap_counitFun]; simp [Carrier.algebraMap_apply])

@[scoped simp] private theorem algebraMap_counitAlg (f : Carrier F L N) :
    algebraMap F L (counitAlg F L N f) = (f : N → L) 0 := algebraMap_counitFun F L N f

private theorem ofId_comp_counitAlg : (Algebra.ofId F L).comp (counitAlg F L N) = ev F L (0 : N) := by
  ext f
  simp [counitAlg, Algebra.ofId_apply, algebraMap_counitFun]

section withN
variable (hN : ∀ x : N, IsOpen (MulAction.stabilizer (L ≃ₐ[F] L) x : Set (L ≃ₐ[F] L))) [Finite N]
include hN

private noncomputable def prodEquiv : Carrier F L N ⊗[F] Carrier F L N ≃ₐ[F] Carrier F L (N × N) :=
  AlgEquiv.ofBijective (pm F L N N) (pm_bijective F L N N hN hN)

@[scoped simp] private theorem prodEquiv_apply (t : Carrier F L N ⊗[F] Carrier F L N) :
    prodEquiv F L N hN t = pm F L N N t := rfl

private noncomputable def comulAlg : Carrier F L N →ₐ[F] Carrier F L N ⊗[F] Carrier F L N :=
  (prodEquiv F L N hN).symm.toAlgHom.comp (addPull F L N)

private theorem pm_comulAlg (f : Carrier F L N) :
    pm F L N N (comulAlg F L N hN f) = addPull F L N f := by
  show prodEquiv F L N hN ((prodEquiv F L N hN).symm (addPull F L N f)) = _
  rw [AlgEquiv.apply_symm_apply]

private theorem chi_comulAlg (x y : N) (f : Carrier F L N) :
    chi F L N x y (comulAlg F L N hN f) = (f : N → L) (x + y) := by
  rw [chi_eq_ev_comp_pm, AlgHom.comp_apply, pm_comulAlg]
  rfl

private theorem chi_comp_comulAlg (x y : N) :
    (chi F L N x y).comp (comulAlg F L N hN) = ev F L (x + y) := by
  ext f; exact chi_comulAlg F L N hN x y f

private noncomputable def chi3 (x y z : N) :
    Carrier F L N ⊗[F] (Carrier F L N ⊗[F] Carrier F L N) →ₐ[F] L :=
  Algebra.TensorProduct.lift (ev F L x) (chi F L N y z) (fun _ _ => Commute.all _ _)

private noncomputable def E3 : Carrier F L N ⊗[F] (Carrier F L N ⊗[F] Carrier F L N) →ₐ[F]
    Carrier F L (N × (N × N)) :=
  (pm F L N (N × N)).comp
    (Algebra.TensorProduct.congr (AlgEquiv.refl : Carrier F L N ≃ₐ[F] Carrier F L N)
      (prodEquiv F L N hN)).toAlgHom

private theorem E3_injective : Function.Injective (E3 F L N hN) := by
  have h2 : ∀ z : N × N, IsOpen (MulAction.stabilizer (L ≃ₐ[F] L) z : Set (L ≃ₐ[F] L)) :=
    isOpen_stabilizer_prod F L hN hN
  exact (pm_bijective F L N (N × N) hN h2).1.comp (AlgEquiv.injective _)

private theorem chi3_eq (x y z : N) :
    chi3 F L N x y z = (ev F L (x, (y, z))).comp (E3 F L N hN) := by
  apply Algebra.TensorProduct.ext'
  intro a t
  induction t using TensorProduct.induction_on with
  | zero => simp [Carrier.zero_apply]
  | tmul b c =>
      simp [chi3, E3, Algebra.TensorProduct.lift_tmul, Algebra.TensorProduct.congr_apply,
        Algebra.TensorProduct.map_tmul, coe_pm_tmul, chi_tmul]
  | add s t hs ht => simp only [TensorProduct.tmul_add, map_add, hs, ht]

private theorem algHom_ext_chi3 {B : Type} [Semiring B] [Algebra F B]
    (φ ψ : B →ₐ[F] Carrier F L N ⊗[F] (Carrier F L N ⊗[F] Carrier F L N))
    (h : ∀ x y z : N, (chi3 F L N x y z).comp φ = (chi3 F L N x y z).comp ψ) : φ = ψ := by
  ext b
  apply E3_injective F L N hN
  apply Subtype.ext; funext w
  have := congrArg (fun χ => χ b) (h w.1 w.2.1 w.2.2)
  simpa [chi3_eq F L N hN] using this

private theorem algHom_ext_chi {B : Type} [Semiring B] [Algebra F B]
    (φ ψ : B →ₐ[F] Carrier F L N ⊗[F] Carrier F L N)
    (h : ∀ x y : N, (chi F L N x y).comp φ = (chi F L N x y).comp ψ) : φ = ψ := by
  ext b
  exact ext_of_chi F L N hN (fun x y => congrArg (fun χ => χ b) (h x y))

private theorem coassoc_alg :
    (Algebra.TensorProduct.assoc F F F (Carrier F L N) (Carrier F L N) (Carrier F L N)).toAlgHom.comp
      ((Algebra.TensorProduct.map (comulAlg F L N hN) (.id F (Carrier F L N))).comp (comulAlg F L N hN))
      = (Algebra.TensorProduct.map (.id F (Carrier F L N)) (comulAlg F L N hN)).comp
          (comulAlg F L N hN) := by
  apply algHom_ext_chi3 F L N hN
  intro x y z

  have lhs : ((chi3 F L N x y z).comp
      ((Algebra.TensorProduct.assoc F F F (Carrier F L N) (Carrier F L N) (Carrier F L N)).toAlgHom.comp
        ((Algebra.TensorProduct.map (comulAlg F L N hN) (.id F (Carrier F L N))).comp
          (comulAlg F L N hN)))) = ev F L (x + y + z) := by

    have h1 : (chi3 F L N x y z).comp
        (Algebra.TensorProduct.assoc F F F (Carrier F L N) (Carrier F L N) (Carrier F L N)).toAlgHom =
        Algebra.TensorProduct.lift (chi F L N x y) (ev F L z) (fun _ _ => Commute.all _ _) := by
      apply Algebra.TensorProduct.ext'
      intro t c
      induction t using TensorProduct.induction_on with
      | zero => simp
      | tmul a b =>
          simp [chi3, Algebra.TensorProduct.assoc_tmul, Algebra.TensorProduct.lift_tmul, chi_tmul,
            mul_assoc]
      | add s t hs ht => simp only [TensorProduct.add_tmul, map_add, hs, ht]

    have h2 : (Algebra.TensorProduct.lift (chi F L N x y) (ev F L z)
        (fun _ _ => Commute.all _ _)).comp
          (Algebra.TensorProduct.map (comulAlg F L N hN) (.id F (Carrier F L N))) =
        chi F L N (x + y) z := by
      apply Algebra.TensorProduct.ext'
      intro a b
      simp [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.lift_tmul, chi_comulAlg, chi_tmul]
    calc (chi3 F L N x y z).comp
          ((Algebra.TensorProduct.assoc F F F (Carrier F L N) (Carrier F L N) (Carrier F L N)).toAlgHom.comp
            ((Algebra.TensorProduct.map (comulAlg F L N hN) (.id F (Carrier F L N))).comp
              (comulAlg F L N hN)))
        = (((chi3 F L N x y z).comp
            (Algebra.TensorProduct.assoc F F F (Carrier F L N) (Carrier F L N)
              (Carrier F L N)).toAlgHom).comp
            (Algebra.TensorProduct.map (comulAlg F L N hN) (.id F (Carrier F L N)))).comp
            (comulAlg F L N hN) := by simp only [AlgHom.comp_assoc]
      _ = ev F L (x + y + z) := by rw [h1, h2, chi_comp_comulAlg]
  have rhs : (chi3 F L N x y z).comp
      ((Algebra.TensorProduct.map (.id F (Carrier F L N)) (comulAlg F L N hN)).comp (comulAlg F L N hN))
      = ev F L (x + (y + z)) := by
    have h1 : (chi3 F L N x y z).comp
        (Algebra.TensorProduct.map (.id F (Carrier F L N)) (comulAlg F L N hN)) = chi F L N x (y + z) := by
      apply Algebra.TensorProduct.ext'
      intro a b
      simp [chi3, Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.lift_tmul, chi_comulAlg,
        chi_tmul]
    rw [← AlgHom.comp_assoc, h1, chi_comp_comulAlg]
  rw [lhs, rhs, add_assoc]

private noncomputable def psiL (x : N) : F ⊗[F] Carrier F L N →ₐ[F] L :=
  Algebra.TensorProduct.lift (Algebra.ofId F L) (ev F L x) (fun _ _ => Commute.all _ _)

private noncomputable def psiR (x : N) : Carrier F L N ⊗[F] F →ₐ[F] L :=
  Algebra.TensorProduct.lift (ev F L x) (Algebra.ofId F L) (fun _ _ => Commute.all _ _)

omit hN [IsGalois F L] [Finite N] in
private theorem psiL_eq (x : N) :
    psiL F L N x = (ev F L x).comp (Algebra.TensorProduct.lid F (Carrier F L N)).toAlgHom := by
  apply Algebra.TensorProduct.ext'
  intro c a
  simp [psiL, Algebra.TensorProduct.lift_tmul, Algebra.TensorProduct.lid_tmul, Algebra.ofId_apply,
    Algebra.smul_def, Carrier.mul_apply, Carrier.algebraMap_apply]

omit hN [IsGalois F L] [Finite N] in
private theorem psiR_eq (x : N) :
    psiR F L N x = (ev F L x).comp (Algebra.TensorProduct.rid F F (Carrier F L N)).toAlgHom := by
  apply Algebra.TensorProduct.ext'
  intro a c
  simp [psiR, Algebra.TensorProduct.lift_tmul, Algebra.TensorProduct.rid_tmul, Algebra.ofId_apply,
    Algebra.smul_def, mul_comm, Carrier.mul_apply, Carrier.algebraMap_apply]

omit hN [IsGalois F L] [Finite N] in

private theorem ext_of_ev {f g : Carrier F L N} (h : ∀ x : N, ev F L x f = ev F L x g) : f = g :=
  Subtype.ext (funext h)

omit hN [IsGalois F L] [Finite N] in

private theorem algHom_ext_psiL {B : Type} [Semiring B] [Algebra F B] (φ ψ : B →ₐ[F] F ⊗[F] Carrier F L N)
    (h : ∀ x : N, (psiL F L N x).comp φ = (psiL F L N x).comp ψ) : φ = ψ := by
  ext b
  apply (Algebra.TensorProduct.lid F (Carrier F L N)).injective
  apply Carrier.ext; funext x
  have := congrArg (fun χ => χ b) (h x)
  rw [psiL_eq] at this
  exact this

omit hN [IsGalois F L] [Finite N] in

private theorem algHom_ext_psiR {B : Type} [Semiring B] [Algebra F B] (φ ψ : B →ₐ[F] Carrier F L N ⊗[F] F)
    (h : ∀ x : N, (psiR F L N x).comp φ = (psiR F L N x).comp ψ) : φ = ψ := by
  ext b
  apply (Algebra.TensorProduct.rid F F (Carrier F L N)).injective
  apply Carrier.ext; funext x
  have := congrArg (fun χ => χ b) (h x)
  rw [psiR_eq] at this
  exact this

private theorem rTensor_alg :
    (Algebra.TensorProduct.map (counitAlg F L N) (.id F (Carrier F L N))).comp (comulAlg F L N hN)
      = ((Algebra.TensorProduct.lid F (Carrier F L N)).symm : Carrier F L N →ₐ[F] F ⊗[F] Carrier F L N) := by
  apply algHom_ext_psiL
  intro x
  have h1 : (psiL F L N x).comp (Algebra.TensorProduct.map (counitAlg F L N) (.id F (Carrier F L N))) =
      chi F L N 0 x := by
    apply Algebra.TensorProduct.ext'
    intro a b
    simp [psiL, Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.lift_tmul, chi_tmul, Algebra.ofId_apply,
      counitAlg, algebraMap_counitFun]
  have h2 : (psiL F L N x).comp ((Algebra.TensorProduct.lid F (Carrier F L N)).symm :
      Carrier F L N →ₐ[F] F ⊗[F] Carrier F L N) = ev F L x := by
    rw [psiL_eq, AlgHom.comp_assoc]
    ext f
    simp
  rw [← AlgHom.comp_assoc, h1, chi_comp_comulAlg, zero_add, h2]

private theorem lTensor_alg :
    (Algebra.TensorProduct.map (.id F (Carrier F L N)) (counitAlg F L N)).comp (comulAlg F L N hN)
      = ((Algebra.TensorProduct.rid F F (Carrier F L N)).symm : Carrier F L N →ₐ[F] Carrier F L N ⊗[F] F) := by
  apply algHom_ext_psiR
  intro x
  have h1 : (psiR F L N x).comp (Algebra.TensorProduct.map (.id F (Carrier F L N)) (counitAlg F L N)) =
      chi F L N x 0 := by
    apply Algebra.TensorProduct.ext'
    intro a b
    simp [psiR, Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.lift_tmul, chi_tmul, Algebra.ofId_apply,
      counitAlg, algebraMap_counitFun]
  have h2 : (psiR F L N x).comp ((Algebra.TensorProduct.rid F F (Carrier F L N)).symm :
      Carrier F L N →ₐ[F] Carrier F L N ⊗[F] F) = ev F L x := by
    rw [psiR_eq, AlgHom.comp_assoc]
    ext f
    simp
  rw [← AlgHom.comp_assoc, h1, chi_comp_comulAlg, add_zero, h2]

@[reducible] private noncomputable def bialgebra : Bialgebra F (Carrier F L N) :=
  Bialgebra.ofAlgHom (comulAlg F L N hN) (counitAlg F L N) (coassoc_alg F L N hN) (rTensor_alg F L N hN)
    (lTensor_alg F L N hN)

private theorem comul_def : (bialgebra F L N hN).comul = (comulAlg F L N hN).toLinearMap := rfl
private theorem counit_def : (bialgebra F L N hN).counit = (counitAlg F L N).toLinearMap := rfl

omit hN [IsGalois F L] [Finite N] in

private theorem ev_comp_mul' (x : N) :
    (ev F L x).toLinearMap ∘ₗ LinearMap.mul' F (Carrier F L N) = (chi F L N x x).toLinearMap := by
  apply TensorProduct.ext'
  intro a b
  simp [chi_tmul, Carrier.mul_apply]

@[reducible] private noncomputable def hopfAlgebra : HopfAlgebra F (Carrier F L N) :=
  { bialgebra F L N hN with
    antipode := (negPull F L N).toLinearMap
    mul_antipode_rTensor_comul := by
      apply LinearMap.ext; intro f
      apply ext_of_ev F L N; intro x
      show ((ev F L x).toLinearMap ∘ₗ LinearMap.mul' F (Carrier F L N))
          (((negPull F L N).toLinearMap.rTensor (Carrier F L N)) (comulAlg F L N hN f)) =
        ev F L x (algebraMap F (Carrier F L N) (counitAlg F L N f))
      rw [ev_comp_mul']
      have h1 : ∀ t : Carrier F L N ⊗[F] Carrier F L N,
          chi F L N x x (((negPull F L N).toLinearMap.rTensor (Carrier F L N)) t) = chi F L N (-x) x t := by
        intro t
        induction t using TensorProduct.induction_on with
        | zero => simp
        | tmul a b => simp only [LinearMap.rTensor_tmul, chi_tmul]; rfl
        | add s t hs ht => simp only [map_add, hs, ht]
      rw [AlgHom.toLinearMap_apply, h1, chi_comulAlg, neg_add_cancel, AlgHom.commutes,
        algebraMap_counitAlg]
    mul_antipode_lTensor_comul := by
      apply LinearMap.ext; intro f
      apply ext_of_ev F L N; intro x
      show ((ev F L x).toLinearMap ∘ₗ LinearMap.mul' F (Carrier F L N))
          (((negPull F L N).toLinearMap.lTensor (Carrier F L N)) (comulAlg F L N hN f)) =
        ev F L x (algebraMap F (Carrier F L N) (counitAlg F L N f))
      rw [ev_comp_mul']
      have h1 : ∀ t : Carrier F L N ⊗[F] Carrier F L N,
          chi F L N x x (((negPull F L N).toLinearMap.lTensor (Carrier F L N)) t) = chi F L N x (-x) t := by
        intro t
        induction t using TensorProduct.induction_on with
        | zero => simp
        | tmul a b => simp only [LinearMap.lTensor_tmul, chi_tmul]; rfl
        | add s t hs ht => simp only [map_add, hs, ht]
      rw [AlgHom.toLinearMap_apply, h1, chi_comulAlg, add_neg_cancel, AlgHom.commutes,
        algebraMap_counitAlg] }

private theorem isCocomm : @Coalgebra.IsCocomm F (Carrier F L N) _ _ _ (bialgebra F L N hN).toCoalgebra := by
  letI := bialgebra F L N hN
  refine ⟨?_⟩
  apply LinearMap.ext; intro f
  apply ext_of_chi F L N hN; intro x y
  show chi F L N x y ((TensorProduct.comm F (Carrier F L N) (Carrier F L N)) (comulAlg F L N hN f)) =
    chi F L N x y (comulAlg F L N hN f)
  have h1 : ∀ t : Carrier F L N ⊗[F] Carrier F L N,
      chi F L N x y (TensorProduct.comm F (Carrier F L N) (Carrier F L N) t) = chi F L N y x t := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [TensorProduct.comm_tmul, chi_tmul, mul_comm]
    | add s t hs ht => simp only [map_add, hs, ht]
  rw [h1, chi_comulAlg, chi_comulAlg, add_comm]

private theorem carrier_finite : Module.Finite F (Carrier F L N) := eqvFun_finite F L N hN

private noncomputable def evEquiv : N ≃ (Carrier F L N →ₐ[F] L) :=
  Equiv.ofBijective (fun x => ev F L x) (evalPt_bijective F L N hN)

@[scoped simp] private theorem evEquiv_apply (x : N) : evEquiv F L N hN x = ev F L x := rfl

private noncomputable def pointsEquiv : WithConv (Carrier F L N →ₐ[F] L) ≃ N :=
  (⟨WithConv.ofConv, WithConv.toConv, fun _ => rfl, fun _ => rfl⟩ :
    WithConv (Carrier F L N →ₐ[F] L) ≃ (Carrier F L N →ₐ[F] L)).trans (evEquiv F L N hN).symm

private theorem pointsEquiv_toConv_ev (x : N) : pointsEquiv F L N hN (WithConv.toConv (ev F L x)) = x := by
  simp [pointsEquiv, Equiv.symm_apply_eq]

private theorem ev_pointsEquiv (φ : WithConv (Carrier F L N →ₐ[F] L)) : ev F L (pointsEquiv F L N hN φ) = φ.ofConv := by
  obtain ⟨x, hx⟩ := (evalPt_bijective F L N hN).2 φ.ofConv
  have : φ = WithConv.toConv (ev F L x) := by
    apply WithConv.ofConv_injective; exact hx.symm
  subst this
  rw [pointsEquiv_toConv_ev]

private theorem pointsEquiv_mul :
    letI := hopfAlgebra F L N hN
    ∀ f g : WithConv (Carrier F L N →ₐ[F] L),
      pointsEquiv F L N hN (f * g) = pointsEquiv F L N hN f + pointsEquiv F L N hN g := by
  letI := hopfAlgebra F L N hN
  intro f g
  set x := pointsEquiv F L N hN f
  set y := pointsEquiv F L N hN g
  have hf : f = WithConv.toConv (ev F L x) := WithConv.ofConv_injective (ev_pointsEquiv F L N hN f).symm
  have hg : g = WithConv.toConv (ev F L y) := WithConv.ofConv_injective (ev_pointsEquiv F L N hN g).symm
  have hmul : f * g = WithConv.toConv (ev F L (x + y)) := by
    apply WithConv.ofConv_injective
    rw [hf, hg, AlgHom.convMul_def]
    show ((Algebra.TensorProduct.lmul' F).comp
        ((Algebra.TensorProduct.map (ev F L x) (ev F L y)).comp (Bialgebra.comulAlgHom F (Carrier F L N)))) =
      ev F L (x + y)
    rw [← AlgHom.comp_assoc, Algebra.TensorProduct.lmul'_comp_map]
    have : Bialgebra.comulAlgHom F (Carrier F L N) = comulAlg F L N hN := by
      ext a; rfl
    rw [this]
    exact chi_comp_comulAlg F L N hN x y
  rw [hmul, pointsEquiv_toConv_ev]

private theorem pointsEquiv_act :
    letI := hopfAlgebra F L N hN
    ∀ (σ : L ≃ₐ[F] L) (f g : WithConv (Carrier F L N →ₐ[F] L)),
      (∀ a : Carrier F L N, g a = σ (f a)) → pointsEquiv F L N hN g = σ • pointsEquiv F L N hN f := by
  intro σ f g h
  set x := pointsEquiv F L N hN f
  have hf : f = WithConv.toConv (ev F L x) := WithConv.ofConv_injective (ev_pointsEquiv F L N hN f).symm
  have hg : g = WithConv.toConv (ev F L (σ • x)) := by
    apply WithConv.ofConv_injective
    rw [ev_smul]
    ext a
    rw [h a, hf]
    rfl
  rw [hg, pointsEquiv_toConv_ev]

end withN
p2m_reactivate "P2MW.S_HopfAlgebra_exists_hopfAlgebra_withConv_equiv_of_isOpen_stabilizer.GaloisPoints.Carrier"

end hopf
p2m_reactivate "P2MW.S_HopfAlgebra_exists_hopfAlgebra_withConv_equiv_of_isOpen_stabilizer.GaloisPoints.Carrier"

end GaloisPoints
p2m_reactivate "P2MW.S_HopfAlgebra_exists_hopfAlgebra_withConv_equiv_of_isOpen_stabilizer.GaloisPoints.Carrier P2MW.S_HopfAlgebra_exists_hopfAlgebra_withConv_equiv_of_isOpen_stabilizer.GaloisPoints"

theorem solution
    (F L : Type) [Field F] [Field L] [Algebra F L] [IsGalois F L]
    (N : Type) [AddCommGroup N] [Finite N] [DistribMulAction (L ≃ₐ[F] L) N]
    (hN : ∀ x : N, IsOpen (MulAction.stabilizer (L ≃ₐ[F] L) x : Set (L ≃ₐ[F] L))) :
    ∃ (A : Type) (_ : CommRing A) (_ : HopfAlgebra F A),
      Module.Finite F A ∧ Coalgebra.IsCocomm F A ∧
      ∃ e : WithConv (A →ₐ[F] L) ≃ N,
        (∀ f g, e (f * g) = e f + e g) ∧
        ∀ (σ : L ≃ₐ[F] L) (f g : WithConv (A →ₐ[F] L)),
          (∀ a : A, g a = σ (f a)) → e g = σ • e f := by
  exact ⟨GaloisPoints.Carrier F L N, inferInstance, GaloisPoints.hopfAlgebra F L N hN,
      GaloisPoints.carrier_finite F L N hN, GaloisPoints.isCocomm F L N hN, GaloisPoints.pointsEquiv F L N hN,
      GaloisPoints.pointsEquiv_mul F L N hN, GaloisPoints.pointsEquiv_act F L N hN⟩

end S_HopfAlgebra_exists_hopfAlgebra_withConv_equiv_of_isOpen_stabilizer
end P2MW
export P2MW.S_HopfAlgebra_exists_hopfAlgebra_withConv_equiv_of_isOpen_stabilizer (solution)
