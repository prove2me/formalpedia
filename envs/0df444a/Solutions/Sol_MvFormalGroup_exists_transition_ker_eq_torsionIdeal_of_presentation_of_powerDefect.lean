-- Prove2me | solution 1 for MvFormalGroup.exists_transition_ker_eq_torsionIdeal_of_presentation_of_powerDefect
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/ad70af33-df77-5733-bb98-9eb91be2e251

import Mathlib
import Definitions.Def_PDivisibleGroup_Basic
import Definitions.Def_MvFormalGroup_BasicV2
import Definitions.Def_MvFormalGroup_EndRingV2
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_PointsV2
import Theorems.Thm_MvFormalGroup_adicEval_add_sub_adicEval_sub_sum_mul_mem_span_sq
import Theorems.Thm_MvFormalGroup_algHom_apply_eq_adicEval_of_forall_apply_X_mem_radical
import Theorems.Thm_IsAdicComplete_exists_isDomain_isDiscreteValuationRing_of_span_natCast_isMaximal
import Theorems.Thm_IsAdicComplete_of_module_finite_free_span_natCast
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MvFormalGroup_exists_transition_ker_eq_torsionIdeal_of_presentation_of_powerDefect

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 80000
set_option Elab.async false

open scoped TensorProduct
open MvPowerSeries

universe u v w

namespace S42LV

section Taylor

variable {R : Type*} [CommRing R] {S : Type*} [CommRing S] [Algebra R S]

theorem adicEval_sub_adicEval_mem_span (J : Ideal S) [IsAdicComplete J S] {d : ℕ}
    (F : MvPowerSeries (Fin d) R) {a b : Fin d → S}
    (ha : ∀ s, a s ∈ J.radical) (hb : ∀ s, b s ∈ J.radical) :
    MvFormalGroup.adicEval J a F - MvFormalGroup.adicEval J b F ∈ Ideal.span (Set.range fun s => a s - b s) := by
  classical
  let Df : Fin d → MvPowerSeries (Fin d) R := fun j =>
    fun m => ((m j + 1 : ℕ) : R) * MvPowerSeries.coeff (m + Finsupp.single j 1) F
  have hDf : ∀ (j : Fin d) (m : Fin d →₀ ℕ),
      (Df j).coeff m = ((m j + 1 : ℕ) : R) * F.coeff (m + Finsupp.single j 1) := fun j m => rfl
  have hz : ∀ s, (a - b) s ∈ J.radical := fun s => Ideal.sub_mem _ (ha s) (hb s)
  have hT := MvFormalGroup.adicEval_add_sub_adicEval_sub_sum_mul_mem_span_sq J F Df hDf b (a - b) hb hz
  have hab : b + (a - b) = a := by abel
  rw [hab] at hT
  have hsq : (Ideal.span (Set.range (a - b))) ^ 2 ≤ Ideal.span (Set.range fun s => a s - b s) := by
    rw [pow_two]; exact Ideal.mul_le_right
  have hsum : ∑ j, MvFormalGroup.adicEval J b (Df j) * (a - b) j ∈ Ideal.span (Set.range fun s => a s - b s) :=
    Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨j, rfl⟩)
  have := Ideal.add_mem _ (hsq hT) hsum
  rwa [sub_add_cancel] at this

end Taylor

section Descend

variable {R : Type*} [CommRing R] {A : Type*} [CommRing A] [Algebra R A]
  {B : Type*} [CommRing B] [Algebra R B] {C : Type*} [CommRing C] [Algebra R C]

theorem algHom_eq_of_comp_eq {D : Type*} [Semiring D] [Algebra R D] {π : A →ₐ[R] B}
    (hπ : Function.Surjective π) {f g : B →ₐ[R] D} (h : f.comp π = g.comp π) : f = g := by
  refine AlgHom.ext fun b => ?_
  obtain ⟨a, rfl⟩ := hπ b
  exact AlgHom.congr_fun h a

noncomputable def descendAlgHom (π : A →ₐ[R] B) (hπ : Function.Surjective π) (g : A →ₐ[R] C)
    (h : ∀ a, π a = 0 → g a = 0) : B →ₐ[R] C :=
  (Ideal.Quotient.liftₐ (RingHom.ker π) g (fun a ha => h a ha)).comp
    (Ideal.quotientKerAlgEquivOfSurjective hπ).symm.toAlgHom

theorem descendAlgHom_apply (π : A →ₐ[R] B) (hπ : Function.Surjective π) (g : A →ₐ[R] C)
    (h : ∀ a, π a = 0 → g a = 0) (a : A) : descendAlgHom π hπ g h (π a) = g a := by
  have hq : (Ideal.quotientKerAlgEquivOfSurjective hπ).symm (π a) = Ideal.Quotient.mk (RingHom.ker π) a :=
    (Ideal.quotientKerAlgEquivOfSurjective hπ).injective (by simp)
  change Ideal.Quotient.liftₐ (RingHom.ker π) g (fun a ha => h a ha)
    ((Ideal.quotientKerAlgEquivOfSurjective hπ).symm (π a)) = g a
  rw [hq]
  rfl

theorem descendAlgHom_comp (π : A →ₐ[R] B) (hπ : Function.Surjective π) (g : A →ₐ[R] C)
    (h : ∀ a, π a = 0 → g a = 0) : (descendAlgHom π hπ g h).comp π = g :=
  AlgHom.ext (descendAlgHom_apply π hπ g h)

theorem ker_eq_map_of_comp_eq {f : B →ₐ[R] C} {π : A →ₐ[R] B} (hπ : Function.Surjective π)
    {g : A →ₐ[R] C} (h : f.comp π = g) :
    RingHom.ker f = Ideal.map π (RingHom.ker g) := by
  have hk : RingHom.ker g = Ideal.comap π (RingHom.ker f) := by
    ext a; rw [Ideal.mem_comap, RingHom.mem_ker, RingHom.mem_ker, ← AlgHom.comp_apply, h]
  rw [hk, Ideal.map_comap_of_surjective _ hπ]

theorem comap_span_eq_ker_sup_span {A' B' : Type*} [CommRing A'] [CommRing B'] (f : A' →+* B')
    (hf : Function.Surjective f) {ι : Type*} (r : ι → B') (r' : ι → A') (hr : ∀ i, f (r' i) = r i) :
    Ideal.comap f (Ideal.span (Set.range r)) = RingHom.ker f ⊔ Ideal.span (Set.range r') := by
  have hmap : Ideal.map f (Ideal.span (Set.range r')) = Ideal.span (Set.range r) := by
    rw [Ideal.map_span]
    congr 1
    ext b
    constructor
    · rintro ⟨_, ⟨i, rfl⟩, rfl⟩; exact ⟨i, (hr i).symm⟩
    · rintro ⟨i, rfl⟩; exact ⟨r' i, ⟨i, rfl⟩, hr i⟩
  rw [← hmap, Ideal.comap_map_of_surjective' f hf, sup_comm]

end Descend

section SeriesTools

variable {A B : Type*} [CommRing A] [CommRing B] {σ : Type*}

theorem mvPowerSeries_map_surjective (f : A →+* B) (hf : Function.Surjective f) :
    Function.Surjective (MvPowerSeries.map (σ := σ) f) := by
  intro G
  refine ⟨fun m => Function.surjInv hf (G m), ?_⟩
  ext m
  rw [MvPowerSeries.coeff_map]
  exact Function.surjInv_eq hf (G m)

theorem mem_ker_map_iff (f : A →+* B) (F : MvPowerSeries σ A) :
    F ∈ RingHom.ker (MvPowerSeries.map (σ := σ) f) ↔ ∀ m, f (MvPowerSeries.coeff m F) = 0 := by
  rw [RingHom.mem_ker, MvPowerSeries.ext_iff]
  simp only [MvPowerSeries.coeff_map, map_zero]

theorem exists_eq_sum_C_mul_of_forall_coeff_mem {n : ℕ} (e : Fin n → A)
    (F : MvPowerSeries σ A) (hF : ∀ m, MvPowerSeries.coeff m F ∈ Ideal.span (Set.range e)) :
    ∃ G : Fin n → MvPowerSeries σ A, F = ∑ k, MvPowerSeries.C (e k) * G k := by
  choose g hg using fun m => (Submodule.mem_span_range_iff_exists_fun A).1 (hF m)
  refine ⟨fun k => fun m => g m k, ?_⟩
  ext m
  rw [map_sum, ← hg m]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [MvPowerSeries.coeff_C_mul, smul_eq_mul, mul_comm]
  rfl

end SeriesTools

section TaylorGeneral

variable {R : Type*} [CommRing R] {S : Type*} [CommRing S] [Algebra R S]

theorem adicEval_sub_adicEval_mem_span' (J : Ideal S) [IsAdicComplete J S] {σ : Type*} [Finite σ]
    (F : MvPowerSeries σ R) {a b : σ → S}
    (ha : ∀ s, a s ∈ J.radical) (hb : ∀ s, b s ∈ J.radical) :
    MvFormalGroup.adicEval J a F - MvFormalGroup.adicEval J b F ∈ Ideal.span (Set.range fun s => a s - b s) := by
  classical
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin σ

  have hX : MvPowerSeries.HasSubst (fun s : σ => (X (e s) : MvPowerSeries (Fin n) R)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun s => MvPowerSeries.constantCoeff_X (e s)
  have key : ∀ c : σ → S, (∀ s, c s ∈ J.radical) →
      MvFormalGroup.adicEval J c F =
        MvFormalGroup.adicEval J (c ∘ e.symm) (MvPowerSeries.subst (fun s => (X (e s) : MvPowerSeries (Fin n) R)) F) := by
    intro c hc
    have hc' : ∀ k, (c ∘ e.symm) k ∈ J.radical := fun k => hc _
    rw [MvFormalGroup.adicEval_subst J hc' hX]
    congr 1
    funext s
    rw [MvFormalGroup.adicEval_X]
    simp
  rw [key a ha, key b hb]
  have h := adicEval_sub_adicEval_mem_span J (MvPowerSeries.subst (fun s => (X (e s) : MvPowerSeries (Fin n) R)) F)
    (a := a ∘ e.symm) (b := b ∘ e.symm) (fun k => ha _) (fun k => hb _)
  refine Ideal.span_mono ?_ h
  rintro _ ⟨k, rfl⟩
  exact ⟨e.symm k, rfl⟩

end TaylorGeneral

section CoeffTorsion

variable {𝓞 : Type*} [CommRing 𝓞] {A : Type*} [CommRing A] {L' : Type*} [CommRing L'] {σ : Type*}

variable [HopfAlgebra 𝓞 A] [HopfAlgebra 𝓞 L']

theorem apply_mem_torsionIdeal_of_mem (ι' : A →ₐc[𝓞] L') (n : ℕ) {x : A}
    (hx : x ∈ PDivisibleGroup.Hopf.torsionIdeal 𝓞 A n) : ι' x ∈ PDivisibleGroup.Hopf.torsionIdeal 𝓞 L' n := by
  have h : PDivisibleGroup.Hopf.torsionIdeal 𝓞 A n ≤
      (PDivisibleGroup.Hopf.torsionIdeal 𝓞 L' n).comap (ι' : A →ₐ[𝓞] L') := by
    show (PDivisibleGroup.Hopf.augIdeal 𝓞 A).map (PDivisibleGroup.Hopf.nsmulAlgHom 𝓞 A n) ≤ _
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    rw [Ideal.mem_comap, Ideal.mem_comap]
    show ι' (PDivisibleGroup.Hopf.nsmulAlgHom 𝓞 A n a) ∈ _
    rw [← PDivisibleGroup.Hopf.nsmulAlgHom_bialgHom_apply]
    refine PDivisibleGroup.Hopf.nsmulAlgHom_mem_torsionIdeal 𝓞 L' ?_ n
    rw [PDivisibleGroup.Hopf.mem_augIdeal_iff, CoalgHomClass.counit_comp_apply]
    exact (PDivisibleGroup.Hopf.mem_augIdeal_iff 𝓞 A a).1 ha
  exact h hx

theorem apply_mem_torsionIdeal_of_forall_coeff_mem [IsNoetherianRing A]
    (θ' : MvPowerSeries σ A →ₐ[𝓞] L') (ι' : A →ₐc[𝓞] L') (hθC : ∀ e, θ' (MvPowerSeries.C e) = ι' e) (n : ℕ)
    (F : MvPowerSeries σ A) (hF : ∀ m, MvPowerSeries.coeff m F ∈ PDivisibleGroup.Hopf.torsionIdeal 𝓞 A n) :
    θ' F ∈ PDivisibleGroup.Hopf.torsionIdeal 𝓞 L' n := by
  classical
  obtain ⟨k, e, he⟩ := Submodule.fg_iff_exists_fin_generating_family.1
    (IsNoetherian.noetherian (PDivisibleGroup.Hopf.torsionIdeal 𝓞 A n))
  have hF' : ∀ m, MvPowerSeries.coeff m F ∈ Ideal.span (Set.range e) := fun m => by
    show MvPowerSeries.coeff m F ∈ Submodule.span A (Set.range e)
    rw [he]
    exact hF m
  obtain ⟨G, rfl⟩ := exists_eq_sum_C_mul_of_forall_coeff_mem e F hF'
  rw [map_sum]
  refine Ideal.sum_mem _ fun j _ => ?_
  rw [map_mul, hθC]
  refine Ideal.mul_mem_right _ _ (apply_mem_torsionIdeal_of_mem ι' n ?_)
  have hj : e j ∈ Submodule.span A (Set.range e) := Submodule.subset_span ⟨j, rfl⟩
  rw [he] at hj
  exact hj

theorem isNoetherianRing_of_module_finite (E : Type*) [CommRing E] [Algebra 𝓞 E] [IsNoetherianRing 𝓞]
    [Module.Finite 𝓞 E] : IsNoetherianRing E :=
  IsNoetherianRing.of_finite 𝓞 E

end CoeffTorsion

section AlgHomExt

variable {R : Type*} [CommRing R] {S : Type*} [CommRing S] [Algebra R S]

theorem algHom_ext_of_apply_X_eq (J : Ideal S) [IsAdicComplete J S] {σ : Type*} [Finite σ]
    (f g : MvPowerSeries σ R →ₐ[R] S) (hf : ∀ s, f (X s) ∈ J.radical) (hfg : ∀ s, f (X s) = g (X s)) :
    f = g := by
  apply AlgHom.ext
  intro F
  rw [MvFormalGroup.algHom_apply_eq_adicEval_of_forall_apply_X_mem_radical J f hf F,
    MvFormalGroup.algHom_apply_eq_adicEval_of_forall_apply_X_mem_radical J g (fun s => hfg s ▸ hf s) F]
  congr 1
  funext s
  exact hfg s

end AlgHomExt

section ComulGen

theorem map_comp_comul_eq_comul_comp
    {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) {d : ℕ} (Φ : MvFormalGroup d 𝓞)
    {E E' L L' : Type u} [CommRing E] [CommRing E'] [CommRing L] [CommRing L']
    [HopfAlgebra 𝓞 E] [HopfAlgebra 𝓞 E'] [HopfAlgebra 𝓞 L] [HopfAlgebra 𝓞 L']
    [IsAdicComplete (Ideal.span {(p : L ⊗[𝓞] L)}) (L ⊗[𝓞] L)]
    [IsAdicComplete (Ideal.span {(p : L' ⊗[𝓞] L')}) (L' ⊗[𝓞] L')]
    (st : E' →ₐc[𝓞] E) (ι : E →ₐc[𝓞] L) (ι' : E' →ₐc[𝓞] L')
    (Ψ : MvPowerSeries (Fin d) 𝓞 →ₐ[𝓞] L) (Ψ' : MvPowerSeries (Fin d) 𝓞 →ₐ[𝓞] L')
    (c₂ : Fin d → E ⊗[𝓞] E) (c₂' : Fin d → E' ⊗[𝓞] E')
    (hc₂st : ∀ i, Algebra.TensorProduct.map (st : E' →ₐ[𝓞] E) (st : E' →ₐ[𝓞] E) (c₂' i) = c₂ i)
    (hc₂p' : ∀ i, c₂' i ∈ Ideal.span {(p : E' ⊗[𝓞] E')})
    (hΨrad : ∀ i, Ψ (X i) ∈ (Ideal.span {(p : L)}).radical)
    (hΨ'rad : ∀ i, Ψ' (X i) ∈ (Ideal.span {(p : L')}).radical)
    (hcomul : ∀ i, Coalgebra.comul (R := 𝓞) (Ψ (X i)) =
      MvFormalGroup.adicEval (Ideal.span {(p : L ⊗[𝓞] L)})
        (Sum.elim (fun j => Ψ (X j) ⊗ₜ[𝓞] (1 : L))
          (fun j => MvFormalGroup.adicEval (Ideal.span {(p : L ⊗[𝓞] L)})
            (Sum.elim (fun j => (1 : L) ⊗ₜ[𝓞] Ψ (X j))
              (fun j => Algebra.TensorProduct.map (ι : E →ₐ[𝓞] L) (ι : E →ₐ[𝓞] L) (c₂ j)))
            (Φ.toPowerSeries j)))
        (Φ.toPowerSeries i))
    (hcomul' : ∀ i, Coalgebra.comul (R := 𝓞) (Ψ' (X i)) =
      MvFormalGroup.adicEval (Ideal.span {(p : L' ⊗[𝓞] L')})
        (Sum.elim (fun j => Ψ' (X j) ⊗ₜ[𝓞] (1 : L'))
          (fun j => MvFormalGroup.adicEval (Ideal.span {(p : L' ⊗[𝓞] L')})
            (Sum.elim (fun j => (1 : L') ⊗ₜ[𝓞] Ψ' (X j))
              (fun j => Algebra.TensorProduct.map (ι' : E' →ₐ[𝓞] L') (ι' : E' →ₐ[𝓞] L') (c₂' j)))
            (Φ.toPowerSeries j)))
        (Φ.toPowerSeries i))
    (hgen' : Function.Surjective
      (Algebra.TensorProduct.lift (ι' : E' →ₐ[𝓞] L') Ψ' (fun _ _ => Commute.all _ _)))
    (t₀ : L' →ₐ[𝓞] L) (h1 : ∀ e, t₀ (ι' e) = ι (st e)) (h2 : t₀.comp Ψ' = Ψ) :
    (Algebra.TensorProduct.map t₀ t₀).comp (Bialgebra.comulAlgHom 𝓞 L') = (Bialgebra.comulAlgHom 𝓞 L).comp t₀ := by
  classical

  have map_mem_span : ∀ {A B : Type u} [CommRing A] [CommRing B] {F : Type u} [FunLike F A B] [RingHomClass F A B]
      (φ : F) {x : A}, x ∈ Ideal.span {(p : A)} → φ x ∈ Ideal.span {(p : B)} := by
    intro A B _ _ F _ _ φ x hx
    obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton'.mp hx
    rw [map_mul, map_natCast]
    exact Ideal.mem_span_singleton'.mpr ⟨φ y, rfl⟩
  have map_mem_rad : ∀ {A B : Type u} [CommRing A] [CommRing B] {F : Type u} [FunLike F A B] [RingHomClass F A B]
      (φ : F) {x : A}, x ∈ (Ideal.span {(p : A)}).radical → φ x ∈ (Ideal.span {(p : B)}).radical := by
    intro A B _ _ F _ _ φ x hx
    obtain ⟨k, hk⟩ := hx
    exact ⟨k, by rw [← map_pow]; exact map_mem_span φ hk⟩
  have alg_map_eq : ∀ {A B C D : Type u} [CommRing A] [CommRing B] [CommRing C] [CommRing D]
      [Algebra 𝓞 A] [Algebra 𝓞 B] [Algebra 𝓞 C] [Algebra 𝓞 D] (f : A →ₐ[𝓞] C) (g : B →ₐ[𝓞] D) (x : A ⊗[𝓞] B),
      Algebra.TensorProduct.map f g x = TensorProduct.map f.toLinearMap g.toLinearMap x := by
    intro A B C D _ _ _ _ _ _ _ _ f g x
    induction x using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero]
    | tmul a b => rw [Algebra.TensorProduct.map_tmul, TensorProduct.map_tmul]; rfl
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  have map_map : ∀ {A B C D A' B' : Type u} [CommRing A] [CommRing B] [CommRing C] [CommRing D] [CommRing A'] [CommRing B']
      [Algebra 𝓞 A] [Algebra 𝓞 B] [Algebra 𝓞 C] [Algebra 𝓞 D] [Algebra 𝓞 A'] [Algebra 𝓞 B']
      (f : A →ₐ[𝓞] C) (g : B →ₐ[𝓞] D) (f' : A' →ₐ[𝓞] A) (g' : B' →ₐ[𝓞] B) (x : A' ⊗[𝓞] B'),
      Algebra.TensorProduct.map f g (Algebra.TensorProduct.map f' g' x) =
        Algebra.TensorProduct.map (f.comp f') (g.comp g') x := by
    intro A B C D A' B' _ _ _ _ _ _ _ _ _ _ _ _ f g f' g' x
    induction x using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero, map_zero]
    | tmul a b => rw [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul]; rfl
    | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]
  have comul_coalgHom : ∀ {A B : Type u} [CommRing A] [CommRing B] [HopfAlgebra 𝓞 A] [HopfAlgebra 𝓞 B]
      (φ : A →ₐc[𝓞] B) (a : A), Coalgebra.comul (R := 𝓞) (φ a) =
        Algebra.TensorProduct.map (φ : A →ₐ[𝓞] B) (φ : A →ₐ[𝓞] B) (Coalgebra.comul (R := 𝓞) a) := by
    intro A B _ _ _ _ φ a
    rw [alg_map_eq]
    exact (CoalgHomClass.map_comp_comul_apply φ a).symm
  have h1' : t₀.comp (ι' : E' →ₐ[𝓞] L') = (ι : E →ₐ[𝓞] L).comp (st : E' →ₐ[𝓞] E) := AlgHom.ext fun e => h1 e

  have hι : ∀ a : E', Algebra.TensorProduct.map t₀ t₀ (Coalgebra.comul (R := 𝓞) (ι' a)) =
      Coalgebra.comul (R := 𝓞) (t₀ (ι' a)) := by
    intro a
    rw [comul_coalgHom ι' a, map_map, h1', ← map_map, h1, comul_coalgHom ι (st a), comul_coalgHom st a]

  have hJfg : (Ideal.span {(p : L' ⊗[𝓞] L')}).FG := ⟨{(p : L' ⊗[𝓞] L')}, by rw [Finset.coe_singleton]⟩
  have hφ : ∀ s ∈ Ideal.span {(p : L' ⊗[𝓞] L')},
      Algebra.TensorProduct.map t₀ t₀ s ∈ (Ideal.span {(p : L ⊗[𝓞] L)}).radical :=
    fun s hs => Ideal.le_radical (map_mem_span (Algebra.TensorProduct.map t₀ t₀) hs)
  have ht₀Ψ : ∀ F, t₀ (Ψ' F) = Ψ F := fun F => AlgHom.congr_fun h2 F
  have hΨ : ∀ b, Algebra.TensorProduct.map t₀ t₀ (Coalgebra.comul (R := 𝓞) (Ψ' b)) =
      Coalgebra.comul (R := 𝓞) (Ψ b) := by
    intro b
    have key : ((Algebra.TensorProduct.map t₀ t₀).comp ((Bialgebra.comulAlgHom 𝓞 L').comp Ψ')) =
        (Bialgebra.comulAlgHom 𝓞 L).comp Ψ := by
      refine S42LV.algHom_ext_of_apply_X_eq (Ideal.span {(p : L ⊗[𝓞] L)}) _ _ (fun i => ?_) (fun i => ?_)
      ·
        show Algebra.TensorProduct.map t₀ t₀ (Coalgebra.comul (R := 𝓞) (Ψ' (X i))) ∈ _
        exact map_mem_rad (Algebra.TensorProduct.map t₀ t₀) (map_mem_rad (Bialgebra.comulAlgHom 𝓞 L') (hΨ'rad i))
      · show Algebra.TensorProduct.map t₀ t₀ (Coalgebra.comul (R := 𝓞) (Ψ' (X i))) = Coalgebra.comul (R := 𝓞) (Ψ (X i))
        rw [hcomul' i, hcomul i]

        have hin : ∀ s, Sum.elim (fun j => (1 : L') ⊗ₜ[𝓞] Ψ' (X j))
            (fun j => Algebra.TensorProduct.map (ι' : E' →ₐ[𝓞] L') (ι' : E' →ₐ[𝓞] L') (c₂' j)) s ∈
            (Ideal.span {(p : L' ⊗[𝓞] L')}).radical := by
          rintro (j | j)
          · exact map_mem_rad (Algebra.TensorProduct.includeRight : L' →ₐ[𝓞] L' ⊗[𝓞] L') (hΨ'rad j)
          · exact Ideal.le_radical (map_mem_span _ (hc₂p' j))
        have hout : ∀ s, Sum.elim (fun j => Ψ' (X j) ⊗ₜ[𝓞] (1 : L'))
            (fun j => MvFormalGroup.adicEval (Ideal.span {(p : L' ⊗[𝓞] L')})
              (Sum.elim (fun j => (1 : L') ⊗ₜ[𝓞] Ψ' (X j))
                (fun j => Algebra.TensorProduct.map (ι' : E' →ₐ[𝓞] L') (ι' : E' →ₐ[𝓞] L') (c₂' j)))
              (Φ.toPowerSeries j)) s ∈ (Ideal.span {(p : L' ⊗[𝓞] L')}).radical := by
          rintro (j | j)
          · exact map_mem_rad (Algebra.TensorProduct.includeLeft : L' →ₐ[𝓞] L' ⊗[𝓞] L') (hΨ'rad j)
          · exact MvFormalGroup.adicEval_mem_radical _ hin (Φ.constantCoeff_eq_zero j)
        rw [MvFormalGroup.map_adicEval (R := 𝓞) (S := L' ⊗[𝓞] L') (S' := L ⊗[𝓞] L) (Ideal.span {(p : L' ⊗[𝓞] L')})
          (Ideal.span {(p : L ⊗[𝓞] L)}) (Algebra.TensorProduct.map t₀ t₀) hJfg hφ hout]
        congr 1
        funext s
        rcases s with j | j
        · show Algebra.TensorProduct.map t₀ t₀ (Ψ' (X j) ⊗ₜ[𝓞] (1 : L')) = Ψ (X j) ⊗ₜ[𝓞] (1 : L)
          rw [Algebra.TensorProduct.map_tmul, map_one, ht₀Ψ]
        · show Algebra.TensorProduct.map t₀ t₀ (MvFormalGroup.adicEval _ _ (Φ.toPowerSeries j)) = _
          rw [MvFormalGroup.map_adicEval (R := 𝓞) (S := L' ⊗[𝓞] L') (S' := L ⊗[𝓞] L) (Ideal.span {(p : L' ⊗[𝓞] L')})
            (Ideal.span {(p : L ⊗[𝓞] L)}) (Algebra.TensorProduct.map t₀ t₀) hJfg hφ hin]
          congr 1
          funext s
          rcases s with k | k
          · show Algebra.TensorProduct.map t₀ t₀ ((1 : L') ⊗ₜ[𝓞] Ψ' (X k)) = (1 : L) ⊗ₜ[𝓞] Ψ (X k)
            rw [Algebra.TensorProduct.map_tmul, map_one, ht₀Ψ]
          · show Algebra.TensorProduct.map t₀ t₀ (Algebra.TensorProduct.map (ι' : E' →ₐ[𝓞] L') (ι' : E' →ₐ[𝓞] L')
              (c₂' k)) = Algebra.TensorProduct.map (ι : E →ₐ[𝓞] L) (ι : E →ₐ[𝓞] L) (c₂ k)
            rw [map_map, h1', ← map_map, hc₂st]
    have := AlgHom.congr_fun key b
    simpa [AlgHom.comp_apply] using this

  apply S42LV.algHom_eq_of_comp_eq hgen'
  apply Algebra.TensorProduct.ext'
  intro a b
  simp only [AlgHom.comp_apply, Algebra.TensorProduct.lift_tmul, map_mul]
  show Algebra.TensorProduct.map t₀ t₀ (Coalgebra.comul (R := 𝓞) (ι' a)) *
      Algebra.TensorProduct.map t₀ t₀ (Coalgebra.comul (R := 𝓞) (Ψ' b)) =
    Coalgebra.comul (R := 𝓞) (t₀ (ι' a)) * Coalgebra.comul (R := 𝓞) (t₀ (Ψ' b))
  rw [hι, hΨ, ht₀Ψ]

end ComulGen

end S42LV

set_option maxHeartbeats 1600000 in
open S42LV in
theorem solution
    {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Fact p.Prime] (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞)
    [(Ideal.span {(p : 𝓞)}).IsMaximal] [IsAdicComplete (Ideal.span {(p : 𝓞)}) 𝓞]
    {d : ℕ} (Φ : MvFormalGroup d 𝓞) [Φ.IsComm] (h : ℕ)

    (he : ℕ) (E : ℕ → Type u) [∀ v, CommRing (E v)] [∀ v, HopfAlgebra 𝓞 (E v)]
    [∀ v, Coalgebra.IsCocomm 𝓞 (E v)] [∀ v, Module.Free 𝓞 (E v)] [∀ v, Module.Finite 𝓞 (E v)]
    (st : ∀ v, E (v + 1) →ₐc[𝓞] E v) (hst : ∀ v, Function.Surjective (st v))
    (hrankE : ∀ v, Module.finrank 𝓞 (E v) = p ^ (v * he))
    (hkerE : ∀ v, RingHom.ker (st v) = PDivisibleGroup.Hopf.torsionIdeal 𝓞 (E (v + 1)) (p ^ v))

    (c₂ : ∀ v, Fin d → E v ⊗[𝓞] E v)
    (hc₂st : ∀ v i, Algebra.TensorProduct.map (st v : E (v + 1) →ₐ[𝓞] E v)
        (st v : E (v + 1) →ₐ[𝓞] E v) (c₂ (v + 1) i) = c₂ v i)
    (hc₂p : ∀ v i, c₂ v i ∈ Ideal.span {(p : E v ⊗[𝓞] E v)})

    (C : ∀ v, ℕ → Fin d → E v)
    (hCp : ∀ v n i, C v n i ∈ Ideal.span {(p : E v)})
    (hCcounit : ∀ v n i, Coalgebra.counit (R := 𝓞) (C v n i) = 0)
    (hCst : ∀ v n i, st v (C (v + 1) n i) = C v n i)
    (hCper : ∀ v m i, C v (p ^ v * m) i =
      MvFormalGroup.adicEval (Ideal.span {(p : E v)}) (C v (p ^ v)) (Φ.nthSeries m i))

    (L : ℕ → Type u) [∀ v, CommRing (L v)] [∀ v, HopfAlgebra 𝓞 (L v)]
    [∀ v, Coalgebra.IsCocomm 𝓞 (L v)] [∀ v, Module.Free 𝓞 (L v)] [∀ v, Module.Finite 𝓞 (L v)]
    (ι : ∀ v, E v →ₐc[𝓞] L v) (Ψ : ∀ v, MvPowerSeries (Fin d) 𝓞 →ₐ[𝓞] L v)
    (θ : ∀ v, MvPowerSeries (Fin d) (E v) →ₐ[𝓞] L v)
    (hrankL : ∀ v, Module.finrank 𝓞 (L v) = p ^ (v * h) * Module.finrank 𝓞 (E v))
    (hθs : ∀ v, Function.Surjective (θ v))
    (hθC : ∀ v (e : E v), θ v (MvPowerSeries.C e) = ι v e)
    (hθX : ∀ v i, θ v (X i) = Ψ v (X i))
    (hθker : ∀ v, RingHom.ker (θ v) =
      Ideal.span (Set.range fun i => (Φ.nthSeries (p ^ v) i).map (algebraMap 𝓞 (E v)) -
        MvPowerSeries.C (MvFormalGroup.adicEval (Ideal.span {(p : E v)}) (C v (p ^ v)) (Φ.invSeries i))))
    (hΨrad : ∀ v i, Ψ v (X i) ∈ (Ideal.span {(p : L v)}).radical)
    (hΨeval : ∀ v F, Ψ v F = MvFormalGroup.adicEval (Ideal.span {(p : L v)}) (fun i => Ψ v (X i)) F)
    (hΨcounit : ∀ v i, Coalgebra.counit (R := 𝓞) (Ψ v (X i)) = 0)
    (hgen : ∀ v, Function.Surjective
      (Algebra.TensorProduct.lift (ι v : E v →ₐ[𝓞] L v) (Ψ v) (fun _ _ => Commute.all _ _)))
    (hcomul : ∀ v i, Coalgebra.comul (R := 𝓞) (Ψ v (X i)) =
      MvFormalGroup.adicEval (Ideal.span {(p : L v ⊗[𝓞] L v)})
        (Sum.elim (fun j => Ψ v (X j) ⊗ₜ[𝓞] (1 : L v))
          (fun j => MvFormalGroup.adicEval (Ideal.span {(p : L v ⊗[𝓞] L v)})
            (Sum.elim (fun j => (1 : L v) ⊗ₜ[𝓞] Ψ v (X j))
              (fun j => Algebra.TensorProduct.map (ι v : E v →ₐ[𝓞] L v) (ι v : E v →ₐ[𝓞] L v) (c₂ v j)))
            (Φ.toPowerSeries j)))
        (Φ.toPowerSeries i))
    (hnsmul : ∀ v n i, PDivisibleGroup.Hopf.nsmulAlgHom 𝓞 (L v) n (Ψ v (X i)) =
      MvFormalGroup.adicEval (Ideal.span {(p : L v)})
        (Sum.elim (fun j => MvFormalGroup.adicEval (Ideal.span {(p : L v)}) (fun k => Ψ v (X k)) (Φ.nthSeries n j))
          (fun j => ι v (C v n j)))
        (Φ.toPowerSeries i)) :
    ∃ t : ∀ v, L (v + 1) →ₐc[𝓞] L v,
      (∀ v, Function.Surjective (t v)) ∧
      (∀ v, Module.finrank 𝓞 (L v) = p ^ (v * (h + he))) ∧
      (∀ v, RingHom.ker (t v) = PDivisibleGroup.Hopf.torsionIdeal 𝓞 (L (v + 1)) (p ^ v)) ∧
      (∀ v, (t v).comp (ι (v + 1)) = (ι v).comp (st v)) ∧
      (∀ v, ((t v : L (v + 1) →ₐc[𝓞] L v) : L (v + 1) →ₐ[𝓞] L v).comp (Ψ (v + 1)) = Ψ v) := by
  classical

  obtain ⟨_instDom, _instDVR, -, -⟩ :=
    IsAdicComplete.exists_isDomain_isDiscreteValuationRing_of_span_natCast_isMaximal p hp
  haveI : IsNoetherianRing 𝓞 := inferInstance
  haveI hcE : ∀ v, IsAdicComplete (Ideal.span {(p : E v)}) (E v) := fun v =>
    IsAdicComplete.of_module_finite_free_span_natCast (𝓞 := 𝓞) p (E v)
  haveI hcL : ∀ v, IsAdicComplete (Ideal.span {(p : L v)}) (L v) := fun v =>
    IsAdicComplete.of_module_finite_free_span_natCast (𝓞 := 𝓞) p (L v)
  haveI hcLL : ∀ v, IsAdicComplete (Ideal.span {(p : L v ⊗[𝓞] L v)}) (L v ⊗[𝓞] L v) := fun v =>
    IsAdicComplete.of_module_finite_free_span_natCast (𝓞 := 𝓞) p (L v ⊗[𝓞] L v)
  have hfg : ∀ (T : Type u) [CommRing T], (Ideal.span {(p : T)}).FG := fun T _ =>
    ⟨{(p : T)}, by simp⟩

  have hmapsp : ∀ {T T' : Type u} [CommRing T] [CommRing T'] [Algebra 𝓞 T] [Algebra 𝓞 T'] (φ : T →ₐ[𝓞] T'),
      ∀ s ∈ Ideal.span {(p : T)}, φ s ∈ (Ideal.span {(p : T')}).radical := by
    intro T T' _ _ _ _ φ s hs
    refine Ideal.le_radical ?_
    obtain ⟨t, rfl⟩ := Ideal.mem_span_singleton'.1 hs
    rw [map_mul, map_natCast]
    exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)
  have hsub_rad : ∀ {T : Type u} [CommRing T] {s : T}, s ∈ Ideal.span {(p : T)} → s ∈ (Ideal.span {(p : T)}).radical :=
    fun h => Ideal.le_radical h

  have hrank : ∀ v, Module.finrank 𝓞 (L v) = p ^ (v * (h + he)) := by
    intro v; rw [hrankL, hrankE, ← pow_add, mul_add]

  let P : ∀ v, MvFormalGroup.Points Φ (L v) (Ideal.span {(p : L v)}) := fun v => ⟨fun i => Ψ v (X i), hΨrad v⟩
  let Qc : ∀ v (n : ℕ), MvFormalGroup.Points Φ (E v) (Ideal.span {(p : E v)}) := fun v n =>
    ⟨C v n, fun i => hsub_rad (hCp v n i)⟩
  let Q : ∀ v (n : ℕ), MvFormalGroup.Points Φ (L v) (Ideal.span {(p : L v)}) := fun v n =>
    MvFormalGroup.Points.map (ι v : E v →ₐ[𝓞] L v) (hfg (E v)) (hmapsp _) (Qc v n)
  have hQval : ∀ v n i, (Q v n).val i = ι v (C v n i) := fun v n i => rfl

  have hθmap : ∀ v (F : MvPowerSeries (Fin d) 𝓞), θ v (F.map (algebraMap 𝓞 (E v))) = Ψ v F := by
    intro v F
    let Ψ' : MvPowerSeries (Fin d) 𝓞 →ₐ[𝓞] L v := (θ v).comp (MvPowerSeries.mapAlgHom (Algebra.ofId 𝓞 (E v)))
    have hΨ'X : ∀ i, Ψ' (X i) = Ψ v (X i) := by
      intro i
      show θ v (MvPowerSeries.map (algebraMap 𝓞 (E v)) (X i)) = _
      rw [MvPowerSeries.map_X, hθX]
    have h1 := MvFormalGroup.algHom_apply_eq_adicEval_of_forall_apply_X_mem_radical (Ideal.span {(p : L v)}) Ψ'
      (fun i => (hΨ'X i).symm ▸ hΨrad v i) F
    have h2 : (fun s => Ψ' (X s)) = fun s => Ψ v (X s) := funext hΨ'X
    rw [h2, ← hΨeval] at h1
    exact h1

  have hPQ : ∀ v, p ^ v • P v = - Q v (p ^ v) := by
    intro v
    ext i
    have hmem : (Φ.nthSeries (p ^ v) i).map (algebraMap 𝓞 (E v)) -
        MvPowerSeries.C (MvFormalGroup.adicEval (Ideal.span {(p : E v)}) (C v (p ^ v)) (Φ.invSeries i)) ∈
        RingHom.ker (θ v) := by
      rw [hθker]; exact Ideal.subset_span ⟨i, rfl⟩
    rw [RingHom.mem_ker, map_sub, sub_eq_zero, hθmap, hθC, hΨeval] at hmem
    rw [MvFormalGroup.Points.val_nsmul, MvFormalGroup.Points.val_neg]
    show MvFormalGroup.adicEval _ (fun i => Ψ v (X i)) (Φ.nthSeries (p ^ v) i) = _
    rw [hmem]

    exact MvFormalGroup.map_adicEval (Ideal.span {(p : E v)}) (Ideal.span {(p : L v)}) (ι v : E v →ₐ[𝓞] L v)
      (hfg (E v)) (hmapsp _) (Qc v (p ^ v)).mem_radical (Φ.invSeries i)

  have hkillE : ∀ v (e : E v), PDivisibleGroup.Hopf.nsmulAlgHom 𝓞 (E v) (p ^ v) e =
      algebraMap 𝓞 (E v) (Coalgebra.counit (R := 𝓞) e) := by
    intro v e
    obtain ⟨e', rfl⟩ := hst v e
    have haug := PDivisibleGroup.Hopf.sub_algebraMap_counit_mem_augIdeal 𝓞 (E (v + 1)) e'
    have htor := PDivisibleGroup.Hopf.nsmulAlgHom_mem_torsionIdeal 𝓞 (E (v + 1)) haug (p ^ v)
    rw [← hkerE v, RingHom.mem_ker, map_sub, PDivisibleGroup.Hopf.nsmulAlgHom_algebraMap] at htor
    have h3 := ((map_sub (st v) _ _).symm.trans htor)
    rw [sub_eq_zero] at h3
    rw [PDivisibleGroup.Hopf.nsmulAlgHom_bialgHom_apply, h3, AlgHomClass.commutes, CoalgHomClass.counit_comp_apply]

  have genExt : ∀ (v : ℕ) {D : Type u} [CommRing D] [Algebra 𝓞 D] (f g : L v →ₐ[𝓞] D),
      (∀ e, f (ι v e) = g (ι v e)) → (f.comp (Ψ v) = g.comp (Ψ v)) → f = g := by
    intro v D _ _ f g hι hΨ
    apply algHom_eq_of_comp_eq (hgen v)
    apply Algebra.TensorProduct.ext'
    intro a b
    simp only [AlgHom.comp_apply, Algebra.TensorProduct.lift_tmul, map_mul, BialgHom.coe_toAlgHom]
    rw [hι a, show f (Ψ v b) = g (Ψ v b) from AlgHom.congr_fun hΨ b]

  have hkillL : ∀ v, PDivisibleGroup.Hopf.nsmulAlgHom 𝓞 (L v) (p ^ v) =
      (Algebra.ofId 𝓞 (L v)).comp (Bialgebra.counitAlgHom 𝓞 (L v)) := by
    intro v
    apply genExt v
    · intro e
      rw [PDivisibleGroup.Hopf.nsmulAlgHom_bialgHom_apply, hkillE, AlgHom.comp_apply, Algebra.ofId_apply,
        Bialgebra.counitAlgHom_apply, CoalgHomClass.counit_comp_apply, AlgHomClass.commutes]
    · have hz : ∀ i, ((PDivisibleGroup.Hopf.nsmulAlgHom 𝓞 (L v) (p ^ v)).comp (Ψ v)) (X i) = 0 := by
        intro i
        have h0 : (p ^ v • P v + Q v (p ^ v)).val i = 0 := by rw [hPQ, neg_add_cancel]; rfl
        rw [MvFormalGroup.Points.val_add, MvFormalGroup.Points.val_nsmul] at h0
        rw [AlgHom.comp_apply, hnsmul]
        exact h0
      refine algHom_ext_of_apply_X_eq (Ideal.span {(p : L v)}) _ _ (fun i => (hz i).symm ▸ Ideal.zero_mem _) ?_
      intro i
      rw [hz i, AlgHom.comp_apply, AlgHom.comp_apply, Bialgebra.counitAlgHom_apply, hΨcounit, map_zero]
  have hkillL' : ∀ v (x : L v), PDivisibleGroup.Hopf.nsmulAlgHom 𝓞 (L v) (p ^ v) x =
      algebraMap 𝓞 (L v) (Coalgebra.counit (R := 𝓞) x) := fun v x => AlgHom.congr_fun (hkillL v) x

  have hQc_p : ∀ v, Qc v (p ^ v * p) = p • Qc v (p ^ v) := by
    intro v
    ext i
    rw [MvFormalGroup.Points.val_nsmul]
    exact hCper v p i
  have hQ_p : ∀ v, Q v (p ^ v * p) = p • Q v (p ^ v) := by
    intro v
    show MvFormalGroup.Points.map _ _ _ (Qc v (p ^ v * p)) = _
    rw [hQc_p, map_nsmul]

  have hstC : ∀ v n (G : MvPowerSeries (Fin d) 𝓞),
      st v (MvFormalGroup.adicEval (Ideal.span {(p : E (v + 1))}) (C (v + 1) n) G) =
        MvFormalGroup.adicEval (Ideal.span {(p : E v)}) (C v n) G := by
    intro v n G
    have h1 := MvFormalGroup.map_adicEval (Ideal.span {(p : E (v + 1))}) (Ideal.span {(p : E v)})
      (st v : E (v + 1) →ₐ[𝓞] E v) (hfg _) (hmapsp _) (Qc (v + 1) n).mem_radical G
    have h2 : (fun s => (st v : E (v + 1) →ₐ[𝓞] E v) ((Qc (v + 1) n).val s)) = C v n := funext fun s => hCst v n s
    rw [h2] at h1
    exact h1
  have level : ∀ v, ∃ t : L (v + 1) →ₐc[𝓞] L v,
      Function.Surjective t ∧
      RingHom.ker t = PDivisibleGroup.Hopf.torsionIdeal 𝓞 (L (v + 1)) (p ^ v) ∧
      t.comp (ι (v + 1)) = (ι v).comp (st v) ∧
      ((t : L (v + 1) →ₐc[𝓞] L v) : L (v + 1) →ₐ[𝓞] L v).comp (Ψ (v + 1)) = Ψ v := by
    intro v

    let mst : MvPowerSeries (Fin d) (E (v + 1)) →ₐ[𝓞] MvPowerSeries (Fin d) (E v) :=
      MvPowerSeries.mapAlgHom (st v : E (v + 1) →ₐ[𝓞] E v)
    have hmst : ∀ F, mst F = MvPowerSeries.map ((st v : E (v + 1) →ₐ[𝓞] E v) : E (v + 1) →+* E v) F :=
      fun F => rfl
    let φ : MvPowerSeries (Fin d) (E (v + 1)) →ₐ[𝓞] L v := (θ v).comp mst
    have hφ : ∀ F, φ F = θ v (MvPowerSeries.map ((st v : E (v + 1) →ₐ[𝓞] E v) : E (v + 1) →+* E v) F) :=
      fun F => rfl
    have hmap_alg : ∀ F : MvPowerSeries (Fin d) 𝓞,
        MvPowerSeries.map ((st v : E (v + 1) →ₐ[𝓞] E v) : E (v + 1) →+* E v) (F.map (algebraMap 𝓞 (E (v + 1)))) =
          F.map (algebraMap 𝓞 (E v)) := by
      intro F
      rw [MvPowerSeries.map_map, AlgHom.comp_algebraMap]

    have hφgen : ∀ i, φ ((Φ.nthSeries (p ^ (v + 1)) i).map (algebraMap 𝓞 (E (v + 1))) -
        MvPowerSeries.C (MvFormalGroup.adicEval (Ideal.span {(p : E (v + 1))}) (C (v + 1) (p ^ (v + 1)))
          (Φ.invSeries i))) = 0 := by
      intro i
      rw [hφ, map_sub, MvPowerSeries.map_C, hmap_alg, map_sub, hθmap, hΨeval]
      rw [show ((st v : E (v + 1) →ₐ[𝓞] E v) : E (v + 1) →+* E v)
          (MvFormalGroup.adicEval (Ideal.span {(p : E (v + 1))}) (C (v + 1) (p ^ (v + 1))) (Φ.invSeries i)) =
          st v (MvFormalGroup.adicEval (Ideal.span {(p : E (v + 1))}) (C (v + 1) (p ^ (v + 1))) (Φ.invSeries i)) from rfl,
        hstC, hθC]

      have key : p ^ (v + 1) • P v = -Q v (p ^ (v + 1)) := by
        rw [show p ^ (v + 1) = p ^ v * p from pow_succ p v]
        conv_lhs => rw [mul_comm, ← smul_smul]
        rw [hPQ, smul_neg, ← hQ_p]
      have := congrArg (fun x : MvFormalGroup.Points Φ (L v) (Ideal.span {(p : L v)}) => x.val i) key
      simp only [MvFormalGroup.Points.val_nsmul, MvFormalGroup.Points.val_neg] at this
      rw [sub_eq_zero, this]
      exact (MvFormalGroup.map_adicEval (Ideal.span {(p : E v)}) (Ideal.span {(p : L v)}) (ι v : E v →ₐ[𝓞] L v)
        (hfg (E v)) (hmapsp _) (Qc v (p ^ (v + 1))).mem_radical (Φ.invSeries i)).symm
    have hkill : ∀ a, θ (v + 1) a = 0 → φ a = 0 := by
      intro a ha
      have ha' : a ∈ RingHom.ker (θ (v + 1)) := ha
      rw [hθker] at ha'
      have hle : Ideal.span (Set.range fun i => (Φ.nthSeries (p ^ (v + 1)) i).map (algebraMap 𝓞 (E (v + 1))) -
          MvPowerSeries.C (MvFormalGroup.adicEval (Ideal.span {(p : E (v + 1))}) (C (v + 1) (p ^ (v + 1)))
            (Φ.invSeries i))) ≤ RingHom.ker φ := by
        rw [Ideal.span_le]
        rintro _ ⟨i, rfl⟩
        exact hφgen i
      exact hle ha'
    let t₀ : L (v + 1) →ₐ[𝓞] L v := descendAlgHom (θ (v + 1)) (hθs (v + 1)) φ hkill
    have ht₀θ : ∀ a, t₀ (θ (v + 1) a) = φ a := descendAlgHom_apply _ _ _ _
    have ht₀ι : ∀ e, t₀ (ι (v + 1) e) = ι v (st v e) := by
      intro e
      rw [← hθC, ht₀θ, hφ, MvPowerSeries.map_C, hθC]
      rfl
    have ht₀ΨX : ∀ i, t₀ (Ψ (v + 1) (X i)) = Ψ v (X i) := by
      intro i
      rw [← hθX, ht₀θ, hφ, MvPowerSeries.map_X, hθX]
    have ht₀Ψ : t₀.comp (Ψ (v + 1)) = Ψ v :=
      algHom_ext_of_apply_X_eq (Ideal.span {(p : L v)}) _ _ (fun i => (ht₀ΨX i).symm ▸ hΨrad v i)
        (fun i => ht₀ΨX i)

    have hcounitEq : (Bialgebra.counitAlgHom 𝓞 (L v)).comp t₀ = Bialgebra.counitAlgHom 𝓞 (L (v + 1)) := by
      apply genExt (v + 1)
      · intro e
        rw [AlgHom.comp_apply, ht₀ι, Bialgebra.counitAlgHom_apply, Bialgebra.counitAlgHom_apply,
          CoalgHomClass.counit_comp_apply, CoalgHomClass.counit_comp_apply, CoalgHomClass.counit_comp_apply]
      · rw [AlgHom.comp_assoc, ht₀Ψ]
        refine algHom_ext_of_apply_X_eq (Ideal.span {(p : 𝓞)}) _ _ (fun i => ?_) (fun i => ?_)
        · rw [AlgHom.comp_apply, Bialgebra.counitAlgHom_apply, hΨcounit]; exact Ideal.zero_mem _
        · rw [AlgHom.comp_apply, AlgHom.comp_apply, Bialgebra.counitAlgHom_apply, Bialgebra.counitAlgHom_apply,
            hΨcounit, hΨcounit]

    have hcomulEq : (Algebra.TensorProduct.map t₀ t₀).comp (Bialgebra.comulAlgHom 𝓞 (L (v + 1))) =
        (Bialgebra.comulAlgHom 𝓞 (L v)).comp t₀ := by
      exact map_comp_comul_eq_comul_comp p Φ (st v) (ι v) (ι (v + 1)) (Ψ v) (Ψ (v + 1)) (c₂ v) (c₂ (v + 1))
        (hc₂st v) (hc₂p (v + 1)) (hΨrad v) (hΨrad (v + 1)) (hcomul v) (hcomul (v + 1)) (hgen (v + 1)) t₀ ht₀ι ht₀Ψ
    let t : L (v + 1) →ₐc[𝓞] L v := BialgHom.ofAlgHom t₀ hcounitEq hcomulEq
    have ht : ∀ x, t x = t₀ x := fun x => rfl
    have htalg : ((t : L (v + 1) →ₐc[𝓞] L v) : L (v + 1) →ₐ[𝓞] L v) = t₀ := AlgHom.ext fun x => rfl

    have hmst_surj : Function.Surjective (MvPowerSeries.map (σ := Fin d) ((st v : E (v + 1) →ₐ[𝓞] E v) : E (v + 1) →+* E v)) :=
      mvPowerSeries_map_surjective _ (hst v)
    have htsurj : Function.Surjective t := by
      intro y
      obtain ⟨a, rfl⟩ := hθs v y
      obtain ⟨F, rfl⟩ := hmst_surj a
      exact ⟨θ (v + 1) F, by rw [ht, ht₀θ, hφ]⟩

    have hker_ge : PDivisibleGroup.Hopf.torsionIdeal 𝓞 (L (v + 1)) (p ^ v) ≤ RingHom.ker t := by
      rw [PDivisibleGroup.Hopf.torsionIdeal, Ideal.map_le_iff_le_comap]
      intro y hy
      rw [Ideal.mem_comap, RingHom.mem_ker, ← PDivisibleGroup.Hopf.nsmulAlgHom_bialgHom_apply t, hkillL',
        CoalgHomClass.counit_comp_apply, (PDivisibleGroup.Hopf.mem_augIdeal_iff 𝓞 _ y).1 hy, map_zero]

    have hker_le : RingHom.ker t ≤ PDivisibleGroup.Hopf.torsionIdeal 𝓞 (L (v + 1)) (p ^ v) := by

      have hkt : RingHom.ker t = Ideal.map (θ (v + 1)) (RingHom.ker φ) := by
        have h1 : RingHom.ker t₀ = Ideal.map (θ (v + 1)) (RingHom.ker φ) :=
          ker_eq_map_of_comp_eq (hθs (v + 1)) (descendAlgHom_comp _ _ _ _)
        rw [← h1]; rfl

      let Rl : Fin d → MvPowerSeries (Fin d) (E (v + 1)) := fun i =>
        (Φ.nthSeries (p ^ v) i).map (algebraMap 𝓞 (E (v + 1))) -
          MvPowerSeries.C (MvFormalGroup.adicEval (Ideal.span {(p : E (v + 1))}) (C (v + 1) (p ^ v)) (Φ.invSeries i))
      have hRl : ∀ i, MvPowerSeries.map ((st v : E (v + 1) →ₐ[𝓞] E v) : E (v + 1) →+* E v) (Rl i) =
          (Φ.nthSeries (p ^ v) i).map (algebraMap 𝓞 (E v)) -
            MvPowerSeries.C (MvFormalGroup.adicEval (Ideal.span {(p : E v)}) (C v (p ^ v)) (Φ.invSeries i)) := by
        intro i
        simp only [Rl, map_sub, MvPowerSeries.map_C, hmap_alg]
        congr 2
        exact hstC v (p ^ v) (Φ.invSeries i)
      have hkφ : RingHom.ker φ = RingHom.ker (MvPowerSeries.map (σ := Fin d) ((st v : E (v + 1) →ₐ[𝓞] E v) : E (v + 1) →+* E v)) ⊔
          Ideal.span (Set.range Rl) := by
        have h1 : RingHom.ker φ = Ideal.comap (MvPowerSeries.map (σ := Fin d) ((st v : E (v + 1) →ₐ[𝓞] E v) : E (v + 1) →+* E v))
            (RingHom.ker (θ v)) := by
          ext F; simp only [RingHom.mem_ker, Ideal.mem_comap, hφ]
        rw [h1, hθker v]
        exact comap_span_eq_ker_sup_span _ hmst_surj _ Rl hRl
      rw [hkt, hkφ, Ideal.map_sup, sup_le_iff]
      constructor
      ·
        haveI : IsNoetherianRing (E (v + 1)) := IsNoetherianRing.of_finite 𝓞 (E (v + 1))
        rw [Ideal.map_le_iff_le_comap]
        intro F hF
        rw [mem_ker_map_iff] at hF
        exact apply_mem_torsionIdeal_of_forall_coeff_mem (θ (v + 1)) (ι (v + 1)) (hθC (v + 1)) (p ^ v) F
          (fun m => by rw [← hkerE v]; exact hF m)
      ·
        rw [Ideal.map_span, Ideal.span_le]
        rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩

        have hθRl : θ (v + 1) (Rl i) = (p ^ v • P (v + 1)).val i - (-Q (v + 1) (p ^ v)).val i := by
          show θ (v + 1) ((Φ.nthSeries (p ^ v) i).map (algebraMap 𝓞 (E (v + 1))) -
            MvPowerSeries.C (MvFormalGroup.adicEval (Ideal.span {(p : E (v + 1))}) (C (v + 1) (p ^ v)) (Φ.invSeries i))) = _
          rw [map_sub, hθmap, hθC, hΨeval, MvFormalGroup.Points.val_nsmul, MvFormalGroup.Points.val_neg]
          congr 1
          exact MvFormalGroup.map_adicEval (Ideal.span {(p : E (v + 1))}) (Ideal.span {(p : L (v + 1))})
            (ι (v + 1) : E (v + 1) →ₐ[𝓞] L (v + 1)) (hfg _) (hmapsp _) (Qc (v + 1) (p ^ v)).mem_radical (Φ.invSeries i)

        have hxval : ∀ j, (p ^ v • P (v + 1) + Q (v + 1) (p ^ v)).val j ∈
            PDivisibleGroup.Hopf.torsionIdeal 𝓞 (L (v + 1)) (p ^ v) := by
          intro j
          have hj : (p ^ v • P (v + 1) + Q (v + 1) (p ^ v)).val j =
              PDivisibleGroup.Hopf.nsmulAlgHom 𝓞 (L (v + 1)) (p ^ v) (Ψ (v + 1) (X j)) := by
            rw [hnsmul, MvFormalGroup.Points.val_add, MvFormalGroup.Points.val_nsmul]
            rfl
          rw [hj]
          exact PDivisibleGroup.Hopf.nsmulAlgHom_mem_torsionIdeal 𝓞 _
            ((PDivisibleGroup.Hopf.mem_augIdeal_iff 𝓞 _ _).2 (hΨcounit (v + 1) j)) (p ^ v)
        have hdecomp : p ^ v • P (v + 1) = (p ^ v • P (v + 1) + Q (v + 1) (p ^ v)) + -Q (v + 1) (p ^ v) := by
          rw [add_neg_cancel_right]
        have hval : (p ^ v • P (v + 1)).val i - (-Q (v + 1) (p ^ v)).val i =
            MvFormalGroup.adicEval (Ideal.span {(p : L (v + 1))})
              (Sum.elim (p ^ v • P (v + 1) + Q (v + 1) (p ^ v)).val (-Q (v + 1) (p ^ v)).val) (Φ.toPowerSeries i) -
            MvFormalGroup.adicEval (Ideal.span {(p : L (v + 1))})
              (Sum.elim (0 : MvFormalGroup.Points Φ (L (v + 1)) (Ideal.span {(p : L (v + 1))})).val
                (-Q (v + 1) (p ^ v)).val) (Φ.toPowerSeries i) := by
          rw [← MvFormalGroup.Points.val_add, ← MvFormalGroup.Points.val_add, zero_add, ← hdecomp]
        rw [hθRl, hval]
        refine (Ideal.span_le.2 ?_) (adicEval_sub_adicEval_mem_span' (Ideal.span {(p : L (v + 1))}) (Φ.toPowerSeries i)
          (a := Sum.elim (p ^ v • P (v + 1) + Q (v + 1) (p ^ v)).val (-Q (v + 1) (p ^ v)).val)
          (b := Sum.elim (0 : MvFormalGroup.Points Φ (L (v + 1)) (Ideal.span {(p : L (v + 1))})).val (-Q (v + 1) (p ^ v)).val)
          (fun s => by rcases s with j | j; exacts [(p ^ v • P (v + 1) + Q (v + 1) (p ^ v)).mem_radical j, (-Q (v + 1) (p ^ v)).mem_radical j])
          (fun s => by rcases s with j | j; exacts [(0 : MvFormalGroup.Points Φ (L (v + 1)) _).mem_radical j, (-Q (v + 1) (p ^ v)).mem_radical j]))
        rintro _ ⟨s, rfl⟩
        rcases s with j | j
        · simp only [Sum.elim_inl, MvFormalGroup.Points.val_zero, sub_zero, SetLike.mem_coe]
          exact hxval j
        · simp only [Sum.elim_inr, sub_self, SetLike.mem_coe]
          exact Ideal.zero_mem _
    refine ⟨t, htsurj, le_antisymm hker_le hker_ge, ?_, ?_⟩
    · exact BialgHom.ext fun e => ht₀ι e
    · rw [htalg]; exact ht₀Ψ
  choose t ht using level
  exact ⟨t, fun v => (ht v).1, hrank, fun v => (ht v).2.1, fun v => (ht v).2.2.1, fun v => (ht v).2.2.2⟩

end S_MvFormalGroup_exists_transition_ker_eq_torsionIdeal_of_presentation_of_powerDefect
end P2MW
export P2MW.S_MvFormalGroup_exists_transition_ker_eq_torsionIdeal_of_presentation_of_powerDefect (solution)
