-- Prove2me | solution 1 for HomogeneousLocalization.Away.flat_fromZeroRingHom_comp_algebraMap_of_forall_flat
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/11728347-60a6-5122-b84f-78dd3cafac9b

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HomogeneousLocalization_Away_flat_fromZeroRingHom_comp_algebraMap_of_forall_flat

set_option autoImplicit false

universe u v

open HomogeneousLocalization

namespace AWAYFLATSOL

open DirectSum

variable {S : Type u} [CommRing S] {A : Type v} [CommRing A] [Algebra S A]
  (𝒜 : ℕ → Submodule S A) [GradedAlgebra 𝒜] {d : ℕ} {f : A} (hf : f ∈ 𝒜 d)

noncomputable abbrev φ (f : A) : S →+* Away 𝒜 f :=
  (HomogeneousLocalization.fromZeroRingHom 𝒜 (Submonoid.powers f)).comp
    ((GradedRing.projZeroRingHom' 𝒜).comp (algebraMap S A))

theorem algebraMap_mem (s : S) : algebraMap S A s ∈ 𝒜 0 := by
  rw [Algebra.algebraMap_eq_smul_one]
  exact Submodule.smul_mem _ s (SetLike.one_mem_graded 𝒜)

theorem val_φ (s : S) :
    (φ 𝒜 f s).val = algebraMap S (Localization (Submonoid.powers f)) s := by
  rw [← Localization.mk_algebraMap]
  simp only [φ, RingHom.comp_apply, HomogeneousLocalization.fromZeroRingHom,
    RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, HomogeneousLocalization.val_mk]
  congr 1
  rw [GradedRing.coe_projZeroRingHom'_apply, GradedRing.projZeroRingHom_apply,
    decompose_of_mem_same 𝒜 (algebraMap_mem 𝒜 s)]

theorem decompose_mul_shift {a b : A} {i j n : ℕ} (ha : a ∈ 𝒜 i) (hn : n = i + j) :
    (decompose 𝒜 (a * b) n : A) = a * decompose 𝒜 b j := by
  subst hn; exact coe_decompose_mul_add_of_left_mem 𝒜 ha

noncomputable def expo (b : Submonoid.powers f) : ℕ := ((Submonoid.mem_powers_iff _ _).1 b.2).choose

theorem pow_expo (b : Submonoid.powers f) : f ^ expo b = (b : A) :=
  ((Submonoid.mem_powers_iff _ _).1 b.2).choose_spec

include hf in
theorem mem_of_pow_eq {b : Submonoid.powers f} {k : ℕ} (hk : f ^ k = (b : A)) :
    (b : A) ∈ 𝒜 (k • d) := hk ▸ SetLike.pow_mem_graded k hf

noncomputable def F' (a : A) (b : Submonoid.powers f) (k : ℕ) (hk : f ^ k = (b : A)) : Away 𝒜 f :=
  HomogeneousLocalization.mk
    { deg := k • d
      num := decompose 𝒜 a (k • d)
      den := ⟨b, mem_of_pow_eq 𝒜 hf hk⟩
      den_mem := b.2 }

theorem val_F' (a : A) (b : Submonoid.powers f) (k : ℕ) (hk : f ^ k = (b : A)) :
    (F' 𝒜 hf a b k hk).val = Localization.mk (decompose 𝒜 a (k • d) : A) b := rfl

include hf in
theorem smul_deg_eq {k k' : ℕ} (h : f ^ k = f ^ k') (h0 : (0 : A) ∉ Submonoid.powers f) :
    k • d = k' • d := by
  refine DirectSum.degree_eq_of_mem_mem 𝒜 (SetLike.pow_mem_graded k hf) (h ▸ SetLike.pow_mem_graded k' hf) ?_
  intro hk; exact h0 ⟨k, hk⟩

theorem F'_indep (a : A) (b : Submonoid.powers f) (k k' : ℕ) (hk : f ^ k = (b : A)) (hk' : f ^ k' = (b : A)) :
    F' 𝒜 hf a b k hk = F' 𝒜 hf a b k' hk' := by
  by_cases h0 : (0 : A) ∈ Submonoid.powers f
  · exact (HomogeneousLocalization.subsingleton 𝒜 h0).elim _ _
  apply HomogeneousLocalization.val_injective
  rw [val_F', val_F', smul_deg_eq 𝒜 hf (hk.trans hk'.symm) h0]

noncomputable def F (a : A) (b : Submonoid.powers f) : Away 𝒜 f := F' 𝒜 hf a b (expo b) (pow_expo b)

theorem val_F (a : A) (b : Submonoid.powers f) :
    (F 𝒜 hf a b).val = Localization.mk (decompose 𝒜 a (expo b • d) : A) b := rfl

theorem F_wd {a c : A} {b e : Submonoid.powers f}
    (h : Localization.r (Submonoid.powers f) (a, b) (c, e)) : F 𝒜 hf a b = F 𝒜 hf c e := by
  rw [Localization.r_iff_exists] at h
  obtain ⟨u, hu⟩ := h
  apply HomogeneousLocalization.val_injective
  rw [val_F, val_F, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  refine ⟨u, ?_⟩
  dsimp only at hu ⊢
  have key := congr_arg
    (fun x : A => (decompose 𝒜 x (expo u • d + (expo e • d + expo b • d)) : A)) hu
  dsimp only at key
  rw [decompose_mul_shift 𝒜 (mem_of_pow_eq 𝒜 hf (pow_expo u)) rfl,
    decompose_mul_shift 𝒜 (mem_of_pow_eq 𝒜 hf (pow_expo e)) rfl,
    decompose_mul_shift 𝒜 (mem_of_pow_eq 𝒜 hf (pow_expo u))
      (show expo u • d + (expo e • d + expo b • d) = expo u • d + (expo b • d + expo e • d) by
        rw [Nat.add_comm (expo e • d)]),
    decompose_mul_shift 𝒜 (mem_of_pow_eq 𝒜 hf (pow_expo b)) rfl] at key
  exact key

noncomputable def retr (x : Localization (Submonoid.powers f)) : Away 𝒜 f :=
  Localization.liftOn x (F 𝒜 hf) (fun h => F_wd 𝒜 hf h)

theorem retr_mk (a : A) (b : Submonoid.powers f) :
    retr 𝒜 hf (Localization.mk a b) = F 𝒜 hf a b :=
  Localization.liftOn_mk _ _ _ _

theorem retr_add (x y : Localization (Submonoid.powers f)) :
    retr 𝒜 hf (x + y) = retr 𝒜 hf x + retr 𝒜 hf y := by
  induction x using Localization.induction_on with
  | H p =>
  induction y using Localization.induction_on with
  | H q =>
  obtain ⟨a, b⟩ := p
  obtain ⟨c, e⟩ := q
  rw [Localization.add_mk, retr_mk, retr_mk, retr_mk]
  by_cases h0 : (0 : A) ∈ Submonoid.powers f
  · exact (HomogeneousLocalization.subsingleton 𝒜 h0).elim _ _
  have hbe : f ^ (expo b + expo e) = ((b * e : Submonoid.powers f) : A) := by
    rw [pow_add, pow_expo, pow_expo]; rfl
  rw [F, F'_indep 𝒜 hf _ (b * e) (expo (b * e)) (expo b + expo e) (pow_expo _) hbe]
  apply HomogeneousLocalization.val_injective
  rw [HomogeneousLocalization.val_add, val_F', val_F, val_F, Localization.add_mk]
  congr 1
  rw [decompose_add, DirectSum.add_apply, Submodule.coe_add,
    decompose_mul_shift 𝒜 (mem_of_pow_eq 𝒜 hf (pow_expo b)) (add_smul _ _ _),
    decompose_mul_shift 𝒜 (mem_of_pow_eq 𝒜 hf (pow_expo e))
      ((add_smul _ _ _).trans (Nat.add_comm _ _))]

theorem val_F_smul (s : S) (a : A) (b : Submonoid.powers f) :
    (F 𝒜 hf (s • a) b).val = s • (F 𝒜 hf a b).val := by
  rw [val_F, val_F, Localization.smul_mk, decompose_smul, DirectSum.smul_apply, Submodule.coe_smul]

end AWAYFLATSOL

open AWAYFLATSOL DirectSum in

theorem solution
    {S : Type u} [CommRing S] {A : Type v} [CommRing A] [Algebra S A]
    (𝒜 : ℕ → Submodule S A) [GradedAlgebra 𝒜]
    (hflat : ∀ n : ℕ, Module.Flat S (𝒜 n))
    {d : ℕ} (f : A) (hf : f ∈ 𝒜 d) :
    ((HomogeneousLocalization.fromZeroRingHom 𝒜 (Submonoid.powers f)).comp
        ((GradedRing.projZeroRingHom' 𝒜).comp (algebraMap S A))).Flat := by
  letI alg : Algebra S (Away 𝒜 f) := (φ 𝒜 f).toAlgebra
  show Module.Flat S (Away 𝒜 f)
  have halg : algebraMap S (Away 𝒜 f) = φ 𝒜 f := RingHom.algebraMap_toAlgebra _

  haveI : ∀ n, Module.Flat S (𝒜 n) := hflat
  haveI : Module.Flat S A := Module.Flat.of_linearEquiv (DirectSum.decomposeLinearEquiv 𝒜)
  haveI : Module.Flat S (Localization (Submonoid.powers f)) := inferInstance

  let i : Away 𝒜 f →ₗ[S] Localization (Submonoid.powers f) :=
    { toFun := HomogeneousLocalization.val
      map_add' := HomogeneousLocalization.val_add
      map_smul' := fun s z => by
        rw [RingHom.id_apply, Algebra.smul_def s z, HomogeneousLocalization.val_mul, halg, val_φ,
          Algebra.smul_def s (HomogeneousLocalization.val z)] }

  let r : Localization (Submonoid.powers f) →ₗ[S] Away 𝒜 f :=
    { toFun := retr 𝒜 hf
      map_add' := retr_add 𝒜 hf
      map_smul' := fun s x => by
        induction x using Localization.induction_on with
        | H p =>
        obtain ⟨a, b⟩ := p
        rw [RingHom.id_apply, Localization.smul_mk, retr_mk, retr_mk]
        apply HomogeneousLocalization.val_injective
        rw [val_F_smul, Algebra.smul_def s (F 𝒜 hf a b), HomogeneousLocalization.val_mul, halg, val_φ,
          Algebra.smul_def s (F 𝒜 hf a b).val] }
  refine Module.Flat.of_retract i r (LinearMap.ext fun z => ?_)
  obtain ⟨n, a, ha, rfl⟩ := HomogeneousLocalization.Away.mk_surjective 𝒜 hf z
  change retr 𝒜 hf (HomogeneousLocalization.Away.mk 𝒜 hf n a ha).val =
    HomogeneousLocalization.Away.mk 𝒜 hf n a ha
  rw [HomogeneousLocalization.Away.val_mk, retr_mk, F,
    F'_indep 𝒜 hf a _ _ n (pow_expo _) rfl]
  apply HomogeneousLocalization.val_injective
  rw [val_F', HomogeneousLocalization.Away.val_mk, decompose_of_mem_same 𝒜 ha]

end S_HomogeneousLocalization_Away_flat_fromZeroRingHom_comp_algebraMap_of_forall_flat
end P2MW
export P2MW.S_HomogeneousLocalization_Away_flat_fromZeroRingHom_comp_algebraMap_of_forall_flat (solution)
