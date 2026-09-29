-- Prove2me | solution 1 for HeckeEis.exists_basis_coeffH1_eq_and_mem_span_and_exists_matrix_of_basis_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/8d22679b-246c-5a0b-bbed-e58e832beac2

import Mathlib
import Definitions.Def_Gamma0CoeffCohomologyEigen
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HeckeEis_exists_basis_coeffH1_eq_and_mem_span_and_exists_matrix_of_basis_eq

set_option autoImplicit false

namespace HeckeEis
p2m_export "HeckeEis" "coeffH1 coeffH1Mk coeffH1Mk_surjective coeffCocycles mem_coeffCocycles_iff coeffCoboundaryMap coeffCoboundaryMap_apply coeffCoboundaries"
namespace Lattice
p2m_open "HeckeEis"

open Module

section Framework

variable {Γ : Type*} [Group Γ] {R : Type*} [CommRing R] {n : Type*} [Fintype n] [DecidableEq n]
variable (M : Γ →* Matrix n n R)
variable (A : Type*) [CommRing A] [Algebra R A]

def act (g : Γ) : (n → A) →ₗ[A] (n → A) := Matrix.mulVecLin ((M g).map (algebraMap R A))

theorem act_apply (g : Γ) (v : n → A) (i : n) : act M A g v i = ∑ j, M g i j • v j := by
  simp only [act, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Matrix.map_apply, Algebra.smul_def]

theorem act_one : act M A 1 = LinearMap.id := by
  apply LinearMap.ext; intro v; funext i
  rw [act_apply, map_one, LinearMap.id_apply]
  simp only [Matrix.one_apply, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ, if_true]

theorem act_mul (g h : Γ) (v : n → A) : act M A (g * h) v = act M A g (act M A h v) := by
  simp only [act, Matrix.mulVecLin_apply, map_mul, Matrix.map_mul, Matrix.mulVec_mulVec]

def Z : Submodule A (Γ → n → A) where
  carrier := {z | ∀ g h : Γ, z (g * h) = z g + act M A g (z h)}
  zero_mem' := by intro g h; simp
  add_mem' := by
    intro z w hz hw g h
    simp only [Pi.add_apply, hz g h, hw g h, map_add]
    abel
  smul_mem' := by
    intro c z hz g h
    simp only [Pi.smul_apply, hz g h, smul_add, map_smul]

theorem mem_Z {z : Γ → n → A} : z ∈ Z M A ↔ ∀ g h : Γ, z (g * h) = z g + act M A g (z h) := Iff.rfl

def cob : (n → A) →ₗ[A] (Γ → n → A) where
  toFun v := fun g => act M A g v - v
  map_add' v w := by funext g; simp only [map_add, Pi.add_apply]; abel
  map_smul' c v := by funext g; simp only [map_smul, Pi.smul_apply, RingHom.id_apply, smul_sub]

theorem cob_apply (v : n → A) (g : Γ) : cob M A v g = act M A g v - v := rfl

def B : Submodule A (Γ → n → A) := LinearMap.range (cob M A)

theorem cob_mem_Z (v : n → A) : cob M A v ∈ Z M A := by
  intro g h
  simp only [cob_apply, act_mul, map_sub]
  abel

theorem B_le_Z : B M A ≤ Z M A := by
  rintro _ ⟨v, rfl⟩; exact cob_mem_Z M A v

abbrev H : Type _ := ↥(Z M A) ⧸ (B M A).comap (Z M A).subtype

abbrev Hmk : ↥(Z M A) →ₗ[A] H M A := ((B M A).comap (Z M A).subtype).mkQ

theorem Hmk_eq_zero_iff (z : ↥(Z M A)) : Hmk M A z = 0 ↔ (z : Γ → n → A) ∈ B M A :=
  (Submodule.Quotient.mk_eq_zero _).trans Submodule.mem_comap

variable {A}

theorem Z_apply_one {z : Γ → n → A} (hz : z ∈ Z M A) : z 1 = 0 := by
  have h := hz 1 1
  rw [mul_one, act_one, LinearMap.id_apply] at h
  have : z 1 + z 1 = z 1 + 0 := by rw [add_zero]; exact h.symm
  exact add_left_cancel this

theorem Z_apply_inv {z : Γ → n → A} (hz : z ∈ Z M A) (g : Γ) : z g⁻¹ = - act M A g⁻¹ (z g) := by
  have h := hz g⁻¹ g
  rw [inv_mul_cancel, Z_apply_one M hz] at h
  exact eq_neg_of_add_eq_zero_left h.symm

theorem Z_eq_zero_of_forall_gen {S : Set Γ} (hS : Subgroup.closure S = ⊤) {z : Γ → n → A}
    (hz : z ∈ Z M A) (h0 : ∀ g ∈ S, z g = 0) : z = 0 := by
  suffices h : ∀ g, z g = 0 from funext h
  intro g
  have hg : g ∈ Subgroup.closure S := by rw [hS]; exact Subgroup.mem_top g
  induction hg using Subgroup.closure_induction with
  | mem x hx => exact h0 x hx
  | one => exact Z_apply_one M hz
  | mul x y _ _ hx hy => rw [hz x y, hx, hy, map_zero, add_zero]
  | inv x _ hx => rw [Z_apply_inv M hz, hx, map_zero, neg_zero]

theorem Z_apply_mem_of_gen {S : Set Γ} (hS : Subgroup.closure S = ⊤) (P : Submodule R A)
    {z : Γ → n → A} (hz : z ∈ Z M A) (hP : ∀ g ∈ S, ∀ i, z g i ∈ P) : ∀ g i, z g i ∈ P := by
  intro g
  have hg : g ∈ Subgroup.closure S := by rw [hS]; exact Subgroup.mem_top g
  induction hg using Subgroup.closure_induction with
  | mem x hx => exact hP x hx
  | one => intro i; rw [Z_apply_one M hz]; exact P.zero_mem
  | mul x y _ _ hx hy =>
    intro i
    rw [hz x y, Pi.add_apply, act_apply]
    exact P.add_mem (hx i) (P.sum_mem fun j _ => P.smul_mem _ (hy j))
  | inv x _ hx =>
    intro i
    rw [Z_apply_inv M hz, Pi.neg_apply, act_apply]
    exact P.neg_mem (P.sum_mem fun j _ => P.smul_mem _ (hx j))

set_option linter.unusedSectionVars false

variable {A' : Type*} [CommRing A'] [Algebra R A']

def push (ψ : A →ₗ[R] A') : (Γ → n → A) →ₗ[R] (Γ → n → A') where
  toFun z := fun g i => ψ (z g i)
  map_add' z w := by funext g i; exact map_add ψ _ _
  map_smul' r z := by funext g i; exact map_smul ψ r _

@[scoped simp] theorem push_apply (ψ : A →ₗ[R] A') (z : Γ → n → A) (g : Γ) (i : n) :
    push ψ z g i = ψ (z g i) := rfl

theorem push_act (ψ : A →ₗ[R] A') (g : Γ) (v : n → A) :
    (fun i => ψ (act M A g v i)) = act M A' g (fun i => ψ (v i)) := by
  funext i
  rw [act_apply, act_apply, map_sum]
  simp only [map_smul]

theorem push_mem_Z (ψ : A →ₗ[R] A') {z : Γ → n → A} (hz : z ∈ Z M A) : push ψ z ∈ Z M A' := by
  intro g h
  funext i
  rw [push_apply, hz g h, Pi.add_apply, map_add, Pi.add_apply, push_apply]
  congr 1
  exact congrFun (push_act M ψ g (z h)) i

theorem push_cob (ψ : A →ₗ[R] A') (v : n → A) :
    push ψ (cob M A v) = cob M A' (fun i => ψ (v i)) := by
  funext g i
  rw [push_apply, cob_apply, cob_apply, Pi.sub_apply, map_sub, Pi.sub_apply]
  congr 1
  exact congrFun (push_act M ψ g v) i

theorem push_mem_B (ψ : A →ₗ[R] A') {z : Γ → n → A} (hz : z ∈ B M A) : push ψ z ∈ B M A' := by
  obtain ⟨v, rfl⟩ := hz
  exact ⟨fun i => ψ (v i), (push_cob M ψ v).symm⟩

theorem push_push {A'' : Type*} [CommRing A''] [Algebra R A''] (ψ : A →ₗ[R] A') (ψ' : A' →ₗ[R] A'')
    (z : Γ → n → A) : push ψ' (push ψ z) = push (ψ' ∘ₗ ψ) z := rfl

variable (K : Type*) [CommRing K] [Algebra R K]

def pushZ : ↥(Z M R) →ₛₗ[algebraMap R K] ↥(Z M K) where
  toFun z := ⟨push (Algebra.linearMap R K) (z : Γ → n → R), push_mem_Z M _ z.2⟩
  map_add' z w := by
    apply Subtype.ext
    exact map_add (push (Algebra.linearMap R K)) _ _
  map_smul' r z := by
    apply Subtype.ext
    funext g i
    change algebraMap R K (r * (z : Γ → n → R) g i) = algebraMap R K r * algebraMap R K ((z : Γ → n → R) g i)
    exact map_mul _ _ _

@[scoped simp] theorem coe_pushZ (z : ↥(Z M R)) :
    ((pushZ M K z : ↥(Z M K)) : Γ → n → K) = push (Algebra.linearMap R K) (z : Γ → n → R) := rfl

def Φc : H M R →ₛₗ[algebraMap R K] H M K :=
  Submodule.mapQ _ _ (pushZ M K) fun z hz => by
    rw [Submodule.mem_comap] at hz ⊢
    exact push_mem_B M (Algebra.linearMap R K) hz

theorem Φc_Hmk (z : ↥(Z M R)) : Φc M K (Hmk M R z) = Hmk M K (pushZ M K z) := rfl

end Framework

end HeckeEis.Lattice
p2m_reactivate "P2MW.S_HeckeEis_exists_basis_coeffH1_eq_and_mem_span_and_exists_matrix_of_basis_eq.HeckeEis P2MW.S_HeckeEis_exists_basis_coeffH1_eq_and_mem_span_and_exists_matrix_of_basis_eq.HeckeEis.Lattice"
p2m_reactivate "P2MW.S_HeckeEis_exists_basis_coeffH1_eq_and_mem_span_and_exists_matrix_of_basis_eq.HeckeEis"

set_option linter.unusedSectionVars false

namespace HeckeEis
p2m_export "HeckeEis" "coeffH1 coeffH1Mk coeffH1Mk_surjective coeffCocycles mem_coeffCocycles_iff coeffCoboundaryMap coeffCoboundaryMap_apply coeffCoboundaries"
namespace Lattice
p2m_open "HeckeEis"

open Module

section Fields

variable {Γ : Type*} [Group Γ] {R : Type*} [CommRing R] {n : Type*} [Fintype n] [DecidableEq n]
variable (M : Γ →* Matrix n n R)
variable (F : Type*) [Field F] [Algebra R F] (K : Type*) [Field K] [Algebra R K] [Algebra F K]
  [IsScalarTower R F K]

abbrev algFK (R : Type*) [CommRing R] (F : Type*) [Field F] [Algebra R F] (K : Type*) [Field K] [Algebra R K]
    [Algebra F K] [IsScalarTower R F K] : F →ₗ[R] K := (Algebra.linearMap F K).restrictScalars R

theorem algFK_comp_algRF : (algFK R F K : F →ₗ[R] K) ∘ₗ Algebra.linearMap R F = Algebra.linearMap R K := by
  apply LinearMap.ext
  intro r
  change algebraMap F K (algebraMap R F r) = algebraMap R K r
  exact (IsScalarTower.algebraMap_apply R F K r).symm

theorem exists_sum_push_of_mem_Z [hΓ : Group.FG Γ] {z : Γ → n → K} (hz : z ∈ Z M K) :
    ∃ (m : ℕ) (k : Fin m → K) (w : Fin m → Γ → n → F),
      (∀ l, w l ∈ Z M F) ∧ z = ∑ l, k l • push (algFK R F K) (w l) := by
  classical
  obtain ⟨S, hS, hSfin⟩ := Group.fg_iff.mp hΓ
  let β := Module.Basis.ofVectorSpace F K

  let zc : Module.Basis.ofVectorSpaceIndex F K → Γ → n → F := fun α => push ((β.coord α).restrictScalars R) z
  have hzc : ∀ α, zc α ∈ Z M F := fun α => push_mem_Z M _ hz

  let A0 : Finset (Module.Basis.ofVectorSpaceIndex F K) :=
    (hSfin.toFinset ×ˢ (Finset.univ : Finset n)).biUnion fun p => (β.repr (z p.1 p.2)).support
  let z' : Γ → n → K := ∑ α ∈ A0, β α • push (algFK R F K) (zc α)
  have hz' : z' ∈ Z M K :=
    (Z M K).sum_mem fun α _ => (Z M K).smul_mem _ (push_mem_Z M _ (hzc α))
  have hzz' : z = z' := by
    rw [← sub_eq_zero]
    apply Z_eq_zero_of_forall_gen M hS ((Z M K).sub_mem hz hz')
    intro g hg
    funext i
    simp only [Pi.sub_apply, Pi.zero_apply, sub_eq_zero]
    simp only [z', Finset.sum_apply, Pi.smul_apply, push_apply, zc, LinearMap.coe_restrictScalars,
      smul_eq_mul]
    have hsupp : (β.repr (z g i)).support ⊆ A0 := by
      intro α hα
      exact Finset.mem_biUnion.mpr ⟨(g, i), Finset.mem_product.mpr ⟨hSfin.mem_toFinset.mpr hg,
        Finset.mem_univ _⟩, hα⟩
    calc z g i = Finsupp.linearCombination F β (β.repr (z g i)) := (β.linearCombination_repr _).symm
      _ = ∑ α ∈ A0, (β.repr (z g i)) α • β α := by
        rw [Finsupp.linearCombination_apply, Finsupp.sum_of_support_subset _ hsupp]
        intro α _; exact zero_smul F _
      _ = ∑ α ∈ A0, β α * (Algebra.linearMap F K) ((β.coord α) (z g i)) := by
        refine Finset.sum_congr rfl fun α _ => ?_
        rw [Algebra.linearMap_apply, Module.Basis.coord_apply, Algebra.smul_def, mul_comm]
  refine ⟨A0.card, fun l => β (A0.equivFin.symm l), fun l => zc (A0.equivFin.symm l),
    fun l => hzc _, ?_⟩
  rw [hzz']
  show ∑ α ∈ A0, β α • push (algFK R F K) (zc α) = _
  rw [← Finset.sum_coe_sort]
  exact (Fintype.sum_equiv A0.equivFin.symm _ _ fun _ => rfl).symm

theorem exists_smul_eq_push_of_mem_Z [hΓ : Group.FG Γ] [IsDomain R] [IsFractionRing R F] {z : Γ → n → F}
    (hz : z ∈ Z M F) :
    ∃ s : R, s ≠ 0 ∧ ∃ zR : Γ → n → R, zR ∈ Z M R ∧ push (Algebra.linearMap R F) zR = algebraMap R F s • z := by
  classical
  obtain ⟨S, hS, hSfin⟩ := Group.fg_iff.mp hΓ
  haveI : Finite S := hSfin.to_subtype
  obtain ⟨⟨s, hs⟩, hint⟩ :=
    IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors R) (fun p : S × n => z p.1 p.2)
  have hs0 : s ≠ 0 := nonZeroDivisors.ne_zero hs
  let P : Submodule R F := LinearMap.range (Algebra.linearMap R F)
  have hsz : algebraMap R F s • z ∈ Z M F := (Z M F).smul_mem _ hz
  have hgen : ∀ g ∈ S, ∀ i, (algebraMap R F s • z) g i ∈ P := by
    intro g hg i
    obtain ⟨r, hr⟩ := hint (⟨g, hg⟩, i)
    refine ⟨r, ?_⟩
    rw [Algebra.linearMap_apply, hr, Pi.smul_apply, Pi.smul_apply]
    simp [Algebra.smul_def]
  have hall := Z_apply_mem_of_gen M hS P hsz hgen
  choose zR hzR using hall
  refine ⟨s, hs0, zR, ?_, ?_⟩
  ·
    have hinj := IsFractionRing.injective R F
    have hpush : push (Algebra.linearMap R F) zR = algebraMap R F s • z := by
      funext g i; exact hzR g i
    have hpZ : push (Algebra.linearMap R F) zR ∈ Z M F := hpush ▸ hsz
    intro g h
    funext i
    apply hinj
    have h1 := congrFun (hpZ g h) i
    rw [Pi.add_apply] at h1
    simp only [push_apply, Algebra.linearMap_apply] at h1
    rw [h1, Pi.add_apply, map_add]
    congr 1
    exact (congrFun (push_act M (Algebra.linearMap R F) g (zR h)) i).symm
  · funext g i; exact hzR g i

theorem exists_rel_of_rel_push {ι : Type*} [Fintype ι] (w : ι → Γ → n → F) (c : ι → K) (l₀ : ι)
    (hc : c l₀ ≠ 0) (hrel : ∑ l, c l • push (algFK R F K) (w l) = 0) :
    ∃ f : ι → F, f l₀ ≠ 0 ∧ ∑ l, f l • w l = 0 := by
  classical
  obtain ⟨π, hπ⟩ := (Algebra.linearMap F K).exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr (algebraMap F K).injective)
  have hπ1 : ∀ f : F, π (algebraMap F K f) = f := fun f => LinearMap.congr_fun hπ f
  let c' : ι → K := fun l => (c l₀)⁻¹ * c l
  have hrel' : ∑ l, c' l • push (algFK R F K) (w l) = 0 := by
    simp_rw [c', mul_smul, ← Finset.smul_sum, hrel, smul_zero]
  refine ⟨fun l => π (c' l), ?_, ?_⟩
  · show π ((c l₀)⁻¹ * c l₀) ≠ 0
    rw [inv_mul_cancel₀ hc, ← (algebraMap F K).map_one, hπ1]
    exact one_ne_zero
  · funext g i
    have h := congrArg (fun x : Γ → n → K => π (x g i)) hrel'
    simp only [Finset.sum_apply, Pi.smul_apply, push_apply, LinearMap.coe_restrictScalars,
      Algebra.linearMap_apply, smul_eq_mul, Pi.zero_apply, map_zero, map_sum] at h
    have h2 : ∑ x, π (c' x) * w x g i = ∑ x, π (c' x * algebraMap F K (w x g i)) :=
      Finset.sum_congr rfl fun l _ => by
        rw [mul_comm (c' l), ← Algebra.smul_def, map_smul, smul_eq_mul, mul_comm]
    simp only [Finset.sum_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul]
    exact h2.trans h

end Fields
p2m_reactivate "P2MW.S_HeckeEis_exists_basis_coeffH1_eq_and_mem_span_and_exists_matrix_of_basis_eq.HeckeEis P2MW.S_HeckeEis_exists_basis_coeffH1_eq_and_mem_span_and_exists_matrix_of_basis_eq.HeckeEis.Lattice"

section MainAux

variable {Γ : Type*} [Group Γ] {R : Type*} [CommRing R] {n : Type*} [Fintype n] [DecidableEq n]
variable (M : Γ →* Matrix n n R)
variable {A : Type*} [CommRing A] [Algebra R A] {A' : Type*} [CommRing A'] [Algebra R A']

theorem push_injective (ψ : A →ₗ[R] A') (hψ : Function.Injective ψ) :
    Function.Injective (push (Γ := Γ) (n := n) ψ) := by
  intro z w h
  funext g i
  exact hψ (congrFun (congrFun h g) i)

theorem map_single_one (ψ : A →ₗ[R] A') (hψ1 : ψ 1 = 1) (j : n) :
    (fun i => ψ (Pi.single (M := fun _ => A) j (1 : A) i)) = Pi.single (M := fun _ => A') j (1 : A') := by
  funext i
  by_cases h : i = j
  · subst h; rw [Pi.single_eq_same, Pi.single_eq_same, hψ1]
  · rw [Pi.single_eq_of_ne h, Pi.single_eq_of_ne h, map_zero]

theorem push_cob_single (ψ : A →ₗ[R] A') (hψ1 : ψ 1 = 1) (j : n) :
    push ψ (cob M A (Pi.single j 1)) = cob M A' (Pi.single j 1) := by
  rw [push_cob, map_single_one ψ hψ1]

variable (A) in
theorem cob_eq_sum_single (v : n → A) : cob M A v = ∑ j, v j • cob M A (Pi.single j 1) := by
  have hv : v = ∑ j, v j • (Pi.single j (1 : A) : n → A) := by
    funext i
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply, Pi.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq, Finset.mem_univ, if_true]
  conv_lhs => rw [hv]
  rw [map_sum]
  simp_rw [map_smul]

end MainAux
p2m_reactivate "P2MW.S_HeckeEis_exists_basis_coeffH1_eq_and_mem_span_and_exists_matrix_of_basis_eq.HeckeEis P2MW.S_HeckeEis_exists_basis_coeffH1_eq_and_mem_span_and_exists_matrix_of_basis_eq.HeckeEis.Lattice"

section Main

variable {Γ : Type*} [Group Γ] [hΓ : Group.FG Γ] {R : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
variable {K : Type*} [Field K] [Algebra R K]
variable {n : Type*} [Fintype n] [DecidableEq n]

theorem pushFK_pushRF (F : Type*) [Field F] [Algebra R F] [Algebra F K] [IsScalarTower R F K]
    (x : Γ → n → R) :
    push (algFK R F K) (push (Algebra.linearMap R F) x) = push (Algebra.linearMap R K) x := by
  rw [push_push, algFK_comp_algRF]

theorem exists_sum_pushRK_of_mem_Z (hRK : Function.Injective (algebraMap R K)) (M : Γ →* Matrix n n R)
    {z : Γ → n → K} (hz : z ∈ Z M K) :
    ∃ (m : ℕ) (k : Fin m → K) (zR : Fin m → ↥(Z M R)),
      z = ∑ l, k l • push (Algebra.linearMap R K) (zR l : Γ → n → R) := by
  classical
  let F := FractionRing R
  letI : Algebra F K := (IsFractionRing.lift hRK : F →+* K).toAlgebra
  haveI : IsScalarTower R F K :=
    IsScalarTower.of_algebraMap_eq fun r => (IsFractionRing.lift_algebraMap hRK r).symm
  obtain ⟨m, k, w, hw, hzw⟩ := exists_sum_push_of_mem_Z M F K hz
  have hint := fun l => exists_smul_eq_push_of_mem_Z M F (hw l)
  choose s hs0 zR hzR hpush using hint
  refine ⟨m, fun l => k l * (algebraMap R K (s l))⁻¹, fun l => ⟨zR l, hzR l⟩, ?_⟩
  rw [hzw]
  refine Finset.sum_congr rfl fun l _ => ?_
  have hsK : algebraMap R K (s l) ≠ 0 := (map_ne_zero_iff _ hRK).mpr (hs0 l)
  have h1 : push (algFK R F K) (algebraMap R F (s l) • w l) =
      algebraMap R K (s l) • push (algFK R F K) (w l) := by
    funext g i
    simp only [push_apply, Pi.smul_apply, LinearMap.coe_restrictScalars, Algebra.linearMap_apply,
      smul_eq_mul, map_mul]
    rw [← IsScalarTower.algebraMap_apply]
  show k l • push (algFK R F K) (w l) = (k l * (algebraMap R K (s l))⁻¹) • push (Algebra.linearMap R K) (zR l)
  rw [mul_smul, ← pushFK_pushRF F, hpush, h1, smul_smul ((algebraMap R K) (s l))⁻¹, inv_mul_cancel₀ hsK,
    one_smul]

theorem main (hRK : Function.Injective (algebraMap R K)) (M : Γ →* Matrix n n R) :
    ∃ (t : ℕ) (b : Fin t → H M R) (c : Module.Basis (Fin t) K (H M K)),
      (∀ i, c i = Φc M K (b i)) ∧
        ∀ x : H M R, ∃ r : Fin t → R, Φc M K x = ∑ i, algebraMap R K (r i) • c i := by
  classical
  let F := FractionRing R
  letI : Algebra F K := (IsFractionRing.lift hRK : F →+* K).toAlgebra
  haveI : IsScalarTower R F K :=
    IsScalarTower.of_algebraMap_eq fun r => (IsFractionRing.lift_algebraMap hRK r).symm
  obtain ⟨S, hS, hSfin⟩ := Group.fg_iff.mp hΓ
  haveI : Finite S := hSfin.to_subtype

  haveI : Module.Finite R ↥(Z M R) := by
    let ev : ↥(Z M R) →ₗ[R] (S → n → R) :=
      { toFun := fun z g => (z : Γ → n → R) g
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    refine Module.Finite.of_injective ev fun z w hzw => ?_
    apply Subtype.ext
    rw [← sub_eq_zero]
    refine Z_eq_zero_of_forall_gen M hS ((Z M R).sub_mem z.2 w.2) fun g hg => ?_
    have h := congrFun hzw ⟨g, hg⟩
    change (z : Γ → n → R) g = (w : Γ → n → R) g at h
    rw [Pi.sub_apply, h, sub_self]

  let Tor := Submodule.torsion R (H M R)
  let t := Module.finrank R (H M R ⧸ Tor)
  let cbar : Module.Basis (Fin t) R (H M R ⧸ Tor) := Module.finBasis R _
  have hlift := fun i => Submodule.mkQ_surjective Tor (cbar i)
  choose b hb using hlift
  have hliftZ := fun i => Submodule.mkQ_surjective ((B M R).comap (Z M R).subtype) (b i)
  choose zb hzb using hliftZ

  have hΦtor : ∀ x ∈ Tor, Φc M K x = 0 := by
    intro x hx
    obtain ⟨⟨a, ha⟩, hax⟩ := (Submodule.mem_torsion_iff x).mp hx
    have hax' : a • x = 0 := hax
    have h1 : algebraMap R K a • Φc M K x = 0 := by
      rw [← LinearMap.map_smulₛₗ, hax', map_zero]
    exact (smul_eq_zero.mp h1).resolve_left ((map_ne_zero_iff _ hRK).mpr (nonZeroDivisors.ne_zero ha))

  have hcomb : ∀ x : H M R,
      Φc M K x = ∑ i, algebraMap R K (cbar.repr (Tor.mkQ x) i) • Φc M K (b i) := by
    intro x
    have hx : x - ∑ i, cbar.repr (Tor.mkQ x) i • b i ∈ Tor := by
      rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply, map_sub, map_sum]
      simp_rw [map_smul, hb]
      rw [cbar.sum_repr, sub_self]
    have h0 := hΦtor _ hx
    rw [map_sub, sub_eq_zero] at h0
    rw [h0, map_sum]
    simp_rw [LinearMap.map_smulₛₗ]
  have hHmk_zb : ∀ i, Hmk M K (pushZ M K (zb i)) = Φc M K (b i) := fun i => by
    rw [← Φc_Hmk, ← hzb i]

  have hspan : ⊤ ≤ Submodule.span K (Set.range fun i => Φc M K (b i)) := by
    intro y _
    obtain ⟨zK, rfl⟩ := Submodule.mkQ_surjective ((B M K).comap (Z M K).subtype) y
    obtain ⟨m, k, zR, hsum⟩ := exists_sum_pushRK_of_mem_Z hRK M zK.2
    have hzK : zK = ∑ l, k l • pushZ M K (zR l) := by
      apply Subtype.ext
      rw [hsum, Submodule.coe_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [Submodule.coe_smul, coe_pushZ]
    rw [hzK, map_sum]
    refine Submodule.sum_mem _ fun l _ => ?_
    rw [map_smul]
    refine Submodule.smul_mem _ _ ?_
    have : ((B M K).comap (Z M K).subtype).mkQ (pushZ M K (zR l)) = Φc M K (Hmk M R (zR l)) := rfl
    rw [this, hcomb]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

  have hind : LinearIndependent K fun i => Φc M K (b i) := by
    rw [Fintype.linearIndependent_iff]
    intro kc hrel
    by_contra hne
    push Not at hne
    obtain ⟨i₀, hi₀⟩ := hne

    have h1 : Hmk M K (∑ i, kc i • pushZ M K (zb i)) = 0 := by
      rw [map_sum]
      simp_rw [map_smul, hHmk_zb]
      exact hrel
    rw [Hmk_eq_zero_iff] at h1
    obtain ⟨v, hv⟩ := h1
    rw [Submodule.coe_sum] at hv

    let u : Fin t ⊕ n → Γ → n → R := Sum.elim (fun i => (zb i : Γ → n → R)) fun j => cob M R (Pi.single j 1)
    let w : Fin t ⊕ n → Γ → n → F := fun l => push (Algebra.linearMap R F) (u l)
    let c : Fin t ⊕ n → K := Sum.elim kc fun j => - v j
    have hrelK : ∑ l, c l • push (algFK R F K) (w l) = 0 := by
      simp only [w, pushFK_pushRF F]
      rw [Fintype.sum_sum_type]
      simp only [c, u, Sum.elim_inl, Sum.elim_inr]
      have hA : ∑ i, kc i • push (Algebra.linearMap R K) (zb i : Γ → n → R) =
          ∑ i, ((kc i • pushZ M K (zb i) : ↥(Z M K)) : Γ → n → K) :=
        Finset.sum_congr rfl fun i _ => by rw [Submodule.coe_smul, coe_pushZ]
      have hB : ∑ j, -v j • push (Algebra.linearMap R K) (cob M R (Pi.single j 1)) = - cob M K v := by
        rw [cob_eq_sum_single M K v, ← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [neg_smul, push_cob_single M _ (by exact (algebraMap R K).map_one)]
      rw [hA, hB, ← hv, add_neg_cancel]
    obtain ⟨f, hf0, hrelF⟩ := exists_rel_of_rel_push F K w c (Sum.inl i₀) hi₀ hrelK

    obtain ⟨⟨s, hs⟩, hint⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors R) f
    choose r hr using hint

    have hrelR : ∑ l, r l • u l = 0 := by
      apply push_injective (Algebra.linearMap R F) (IsFractionRing.injective R F)
      rw [map_sum, map_zero]
      have h3 : ∀ l, push (Algebra.linearMap R F) (r l • u l) = (s • f l) • w l := fun l => by
        rw [map_smul, ← algebraMap_smul F (r l), hr l]
      simp_rw [h3, smul_assoc, ← Finset.smul_sum, hrelF, smul_zero]
    rw [Fintype.sum_sum_type] at hrelR
    simp only [u, Sum.elim_inl, Sum.elim_inr] at hrelR

    have hBR : ((∑ i, r (Sum.inl i) • zb i : ↥(Z M R)) : Γ → n → R) ∈ B M R := by
      rw [Submodule.coe_sum]
      simp only [Submodule.coe_smul]
      rw [eq_neg_of_add_eq_zero_left hrelR]
      exact (B M R).neg_mem ((B M R).sum_mem fun j _ => (B M R).smul_mem _ ⟨Pi.single j 1, rfl⟩)

    have hzb' : ∀ i, Hmk M R (zb i) = b i := hzb
    have hH : ∑ i, r (Sum.inl i) • b i = 0 := by
      have h4 := (Hmk_eq_zero_iff M R _).mpr hBR
      rw [map_sum] at h4
      simp_rw [map_smul, hzb'] at h4
      exact h4
    have hbar : ∑ i, r (Sum.inl i) • cbar i = 0 := by
      have h5 := congrArg Tor.mkQ hH
      rw [map_sum, map_zero] at h5
      simp_rw [map_smul, hb] at h5
      exact h5
    have hr0 : r (Sum.inl i₀) = 0 := (Fintype.linearIndependent_iff.mp cbar.linearIndependent _ hbar) i₀

    have h6 := hr (Sum.inl i₀)
    rw [hr0, map_zero] at h6
    have hsF : algebraMap R F s ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hs
    apply hf0
    have h7 : algebraMap R F s * f (Sum.inl i₀) = 0 := by
      rw [← Algebra.smul_def]; exact h6.symm
    exact (mul_eq_zero.mp h7).resolve_left hsF

  refine ⟨t, b, Module.Basis.mk hind hspan, fun i => Module.Basis.mk_apply hind hspan i,
    fun x => ⟨fun i => cbar.repr (Tor.mkQ x) i, ?_⟩⟩
  rw [hcomb x]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Module.Basis.mk_apply]

end Main
p2m_reactivate "P2MW.S_HeckeEis_exists_basis_coeffH1_eq_and_mem_span_and_exists_matrix_of_basis_eq.HeckeEis P2MW.S_HeckeEis_exists_basis_coeffH1_eq_and_mem_span_and_exists_matrix_of_basis_eq.HeckeEis.Lattice"

end HeckeEis.Lattice
p2m_reactivate "P2MW.S_HeckeEis_exists_basis_coeffH1_eq_and_mem_span_and_exists_matrix_of_basis_eq.HeckeEis P2MW.S_HeckeEis_exists_basis_coeffH1_eq_and_mem_span_and_exists_matrix_of_basis_eq.HeckeEis.Lattice"
p2m_reactivate "P2MW.S_HeckeEis_exists_basis_coeffH1_eq_and_mem_span_and_exists_matrix_of_basis_eq.HeckeEis P2MW.S_HeckeEis_exists_basis_coeffH1_eq_and_mem_span_and_exists_matrix_of_basis_eq.HeckeEis.Lattice"

namespace HeckeEis
p2m_export "HeckeEis" "coeffH1 coeffH1Mk coeffH1Mk_surjective coeffCocycles mem_coeffCocycles_iff coeffCoboundaryMap coeffCoboundaryMap_apply coeffCoboundaries"
namespace Lattice
p2m_open "HeckeEis"

open Module

namespace Transport

section Generic

variable {Γ : Type*} [Group Γ] {R : Type*} [CommRing R] {n : Type*} [Fintype n] [DecidableEq n]
variable (M : Γ →* Matrix n n R)
variable {A : Type*} [CommRing A] [Algebra R A]
variable {W : Type*} [AddCommGroup W] [Module A W]
variable (σ : Representation A Γ W) (b : Module.Basis n A W)

variable (Γ) in

private noncomputable def _root_.HeckeEis.Lattice.Transport.coord : (Γ → W) ≃ₗ[A] (Γ → n → A) :=
  LinearEquiv.piCongrRight fun _ : Γ => b.equivFun

p2m_export "HeckeEis.Lattice.Transport" "coord"
omit [Group Γ] [DecidableEq n] in
private theorem _root_.HeckeEis.Lattice.Transport.coord_apply (z : Γ → W) (g : Γ) : coord Γ b z g = b.equivFun (z g) := rfl

p2m_export "HeckeEis.Lattice.Transport" "coord_apply"
omit [Group Γ] [DecidableEq n] in
theorem coord_apply_apply (z : Γ → W) (g : Γ) (i : n) : coord Γ b z g i = b.repr (z g) i := rfl

noncomputable def matrixRep : Γ →* Matrix n n A where
  toFun g := LinearMap.toMatrix b b (σ g)
  map_one' := by rw [map_one]; exact LinearMap.toMatrix_one b
  map_mul' g h := by rw [map_mul]; exact LinearMap.toMatrix_mul b (σ g) (σ h)

theorem matrixRep_apply (g : Γ) : matrixRep σ b g = LinearMap.toMatrix b b (σ g) := rfl

theorem repr_rep_apply (g : Γ) (v : W) (i : n) :
    b.repr (σ g v) i = ∑ j, LinearMap.toMatrix b b (σ g) i j * b.repr v j := by
  have h := LinearMap.toMatrix_mulVec_repr b b (σ g) v
  rw [← h]
  simp [Matrix.mulVec, dotProduct]

def IsMatrixOf : Prop := ∀ g : Γ, LinearMap.toMatrix b b (σ g) = (M g).map (algebraMap R A)

variable {M σ b}

theorem IsMatrixOf.equivFun_rep (hM : IsMatrixOf M σ b) (g : Γ) (v : W) :
    b.equivFun (σ g v) = act M A g (b.equivFun v) := by
  funext i
  rw [Module.Basis.equivFun_apply, act_apply, repr_rep_apply, hM g]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.map_apply, Algebra.smul_def, Module.Basis.equivFun_apply]

theorem IsMatrixOf.coord_mem_Z_iff (hM : IsMatrixOf M σ b) (z : Γ → W) :
    coord Γ b z ∈ Z M A ↔ z ∈ coeffCocycles σ := by
  rw [mem_Z, mem_coeffCocycles_iff]
  refine forall_congr' fun g => forall_congr' fun h => ?_
  rw [coord_apply, coord_apply, coord_apply, ← hM.equivFun_rep, ← map_add]
  exact b.equivFun.injective.eq_iff

theorem IsMatrixOf.map_coeffCocycles (hM : IsMatrixOf M σ b) :
    (coeffCocycles σ).map (coord Γ b : (Γ → W) →ₗ[A] (Γ → n → A)) = Z M A := by
  ext x
  rw [Submodule.mem_map_equiv, ← hM.coord_mem_Z_iff, LinearEquiv.apply_symm_apply]

theorem IsMatrixOf.coord_coeffCoboundaryMap (hM : IsMatrixOf M σ b) (v : W) :
    coord Γ b (coeffCoboundaryMap σ v) = cob M A (b.equivFun v) := by
  funext g
  rw [coord_apply, coeffCoboundaryMap_apply, cob_apply, map_sub, hM.equivFun_rep]

theorem IsMatrixOf.map_coeffCoboundaries (hM : IsMatrixOf M σ b) :
    (coeffCoboundaries σ).map (coord Γ b : (Γ → W) →ₗ[A] (Γ → n → A)) = B M A := by
  apply le_antisymm
  · rintro _ ⟨z, ⟨v, rfl⟩, rfl⟩
    exact ⟨b.equivFun v, (hM.coord_coeffCoboundaryMap v).symm⟩
  · rintro _ ⟨c, rfl⟩
    refine ⟨coeffCoboundaryMap σ (b.equivFun.symm c), ⟨_, rfl⟩, ?_⟩
    change coord Γ b (coeffCoboundaryMap σ (b.equivFun.symm c)) = cob M A c
    rw [hM.coord_coeffCoboundaryMap, LinearEquiv.apply_symm_apply]

noncomputable def IsMatrixOf.coordZ (hM : IsMatrixOf M σ b) : ↥(coeffCocycles σ) ≃ₗ[A] ↥(Z M A) :=
  LinearEquiv.ofSubmodules (coord Γ b) _ _ hM.map_coeffCocycles

theorem IsMatrixOf.coe_coordZ (hM : IsMatrixOf M σ b) (z : ↥(coeffCocycles σ)) :
    ((hM.coordZ z : ↥(Z M A)) : Γ → n → A) = coord Γ b z :=
  LinearEquiv.ofSubmodules_apply (coord Γ b) hM.map_coeffCocycles z

theorem IsMatrixOf.coordZ_apply (hM : IsMatrixOf M σ b) (z : ↥(coeffCocycles σ)) (g : Γ) (i : n) :
    ((hM.coordZ z : ↥(Z M A)) : Γ → n → A) g i = b.repr ((z : Γ → W) g) i := by
  rw [hM.coe_coordZ]; rfl

theorem IsMatrixOf.map_comap_coeffCoboundaries (hM : IsMatrixOf M σ b) :
    ((coeffCoboundaries σ).comap (coeffCocycles σ).subtype).map
        (hM.coordZ : ↥(coeffCocycles σ) →ₗ[A] ↥(Z M A)) =
      (B M A).comap (Z M A).subtype := by
  ext x
  rw [Submodule.mem_map_equiv, Submodule.mem_comap, Submodule.mem_comap, Submodule.subtype_apply,
    Submodule.subtype_apply, ← hM.map_coeffCoboundaries, Submodule.mem_map_equiv, IsMatrixOf.coordZ,
    LinearEquiv.ofSubmodules_symm_apply]

noncomputable def IsMatrixOf.coordH (hM : IsMatrixOf M σ b) : coeffH1 σ ≃ₗ[A] H M A :=
  Submodule.Quotient.equiv _ _ hM.coordZ hM.map_comap_coeffCoboundaries

theorem IsMatrixOf.coordH_mk (hM : IsMatrixOf M σ b) (z : ↥(coeffCocycles σ)) :
    hM.coordH (coeffH1Mk σ z) = Hmk M A (hM.coordZ z) := rfl

variable (σ b) in

theorem isMatrixOf_matrixRep : IsMatrixOf (matrixRep σ b) σ b := by
  intro g
  ext i j
  rw [Matrix.map_apply, matrixRep_apply, Algebra.algebraMap_self, RingHom.id_apply]

end Generic
p2m_reactivate "P2MW.S_HeckeEis_exists_basis_coeffH1_eq_and_mem_span_and_exists_matrix_of_basis_eq.HeckeEis P2MW.S_HeckeEis_exists_basis_coeffH1_eq_and_mem_span_and_exists_matrix_of_basis_eq.HeckeEis.Lattice"

section Card

variable {Γ : Type*} [Group Γ] {R : Type*} [CommRing R] {K : Type*} [CommRing K] [Algebra R K]
variable {Λ : Type*} [AddCommGroup Λ] [Module R Λ] {V : Type*} [AddCommGroup V] [Module K V]
variable {ρR : Representation R Γ Λ} {ρ : Representation K Γ V}
variable {ι : Λ →+ V}
variable {n : Type*} [Fintype n] [DecidableEq n] {bΛ : Module.Basis n R Λ} {bV : Module.Basis n K V}

omit [DecidableEq n] in

theorem repr_iota (hιs : ∀ (r : R) (x : Λ), ι (r • x) = algebraMap R K r • ι x)
    (hb : ∀ j : n, bV j = ι (bΛ j)) (x : Λ) (i : n) :
    bV.repr (ι x) i = algebraMap R K (bΛ.repr x i) := by
  set c : n → K := fun j => algebraMap R K (bΛ.repr x j) with hc
  have hx : ι x = ∑ j, c j • bV j := by
    conv_lhs => rw [← bΛ.sum_repr x]
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hιs, hb]
  have h : bV.equivFun (∑ j, c j • bV j) = c := by
    rw [← bV.equivFun_symm_apply, LinearEquiv.apply_symm_apply]
  rw [hx]
  exact congrFun h i

theorem isMatrixOf_of_iota (hιs : ∀ (r : R) (x : Λ), ι (r • x) = algebraMap R K r • ι x)
    (hιρ : ∀ (γ : Γ) (x : Λ), ι (ρR γ x) = ρ γ (ι x)) (hb : ∀ j : n, bV j = ι (bΛ j)) :
    IsMatrixOf (matrixRep ρR bΛ) ρ bV := by
  intro g
  ext i j
  rw [LinearMap.toMatrix_apply, Matrix.map_apply, matrixRep_apply, LinearMap.toMatrix_apply, hb, ← hιρ,
    repr_iota hιs hb]

theorem coordZ_eq_pushZ (hιs : ∀ (r : R) (x : Λ), ι (r • x) = algebraMap R K r • ι x)
    (hb : ∀ j : n, bV j = ι (bΛ j))
    (hR : IsMatrixOf (matrixRep ρR bΛ) ρR bΛ) (hK : IsMatrixOf (matrixRep ρR bΛ) ρ bV)
    (z : ↥(coeffCocycles ρR)) (w : ↥(coeffCocycles ρ))
    (hw : ∀ γ : Γ, (w : Γ → V) γ = ι ((z : Γ → Λ) γ)) :
    hK.coordZ w = pushZ (matrixRep ρR bΛ) K (hR.coordZ z) := by
  apply Subtype.ext
  funext g i
  rw [hK.coordZ_apply, coe_pushZ, push_apply, hR.coordZ_apply, Algebra.linearMap_apply, hw,
    repr_iota hιs hb]

theorem coordH_comp_eq_Φc (hιs : ∀ (r : R) (x : Λ), ι (r • x) = algebraMap R K r • ι x)
    (hb : ∀ j : n, bV j = ι (bΛ j))
    (hR : IsMatrixOf (matrixRep ρR bΛ) ρR bΛ) (hK : IsMatrixOf (matrixRep ρR bΛ) ρ bV)
    (Φ : coeffH1 ρR →+ coeffH1 ρ)
    (hΦ : ∀ z : ↥(coeffCocycles ρR), ∃ w : ↥(coeffCocycles ρ),
      (∀ γ : Γ, (w : Γ → V) γ = ι ((z : Γ → Λ) γ)) ∧ Φ (coeffH1Mk ρR z) = coeffH1Mk ρ w)
    (x : coeffH1 ρR) :
    hK.coordH (Φ x) = Φc (matrixRep ρR bΛ) K (hR.coordH x) := by
  obtain ⟨z, rfl⟩ := coeffH1Mk_surjective ρR x
  obtain ⟨w, hw, hΦz⟩ := hΦ z
  rw [hΦz, hK.coordH_mk, hR.coordH_mk, Φc_Hmk, coordZ_eq_pushZ hιs hb hR hK z w hw]

theorem map_smul_of_induced (hιs : ∀ (r : R) (x : Λ), ι (r • x) = algebraMap R K r • ι x)
    (Φ : coeffH1 ρR →+ coeffH1 ρ)
    (hΦ : ∀ z : ↥(coeffCocycles ρR), ∃ w : ↥(coeffCocycles ρ),
      (∀ γ : Γ, (w : Γ → V) γ = ι ((z : Γ → Λ) γ)) ∧ Φ (coeffH1Mk ρR z) = coeffH1Mk ρ w)
    (r : R) (x : coeffH1 ρR) : Φ (r • x) = algebraMap R K r • Φ x := by
  obtain ⟨z, rfl⟩ := coeffH1Mk_surjective ρR x
  obtain ⟨w, hw, hΦz⟩ := hΦ z
  obtain ⟨w', hw', hΦz'⟩ := hΦ (r • z)
  have : w' = algebraMap R K r • w := by
    apply Subtype.ext
    funext γ
    rw [hw', Submodule.coe_smul, Pi.smul_apply, Submodule.coe_smul, Pi.smul_apply, hιs, hw]
  rw [← map_smul, hΦz', hΦz, this, map_smul]

end Card
p2m_reactivate "P2MW.S_HeckeEis_exists_basis_coeffH1_eq_and_mem_span_and_exists_matrix_of_basis_eq.HeckeEis P2MW.S_HeckeEis_exists_basis_coeffH1_eq_and_mem_span_and_exists_matrix_of_basis_eq.HeckeEis.Lattice"

end Transport
p2m_reactivate "P2MW.S_HeckeEis_exists_basis_coeffH1_eq_and_mem_span_and_exists_matrix_of_basis_eq.HeckeEis P2MW.S_HeckeEis_exists_basis_coeffH1_eq_and_mem_span_and_exists_matrix_of_basis_eq.HeckeEis.Lattice"

end HeckeEis.Lattice
p2m_reactivate "P2MW.S_HeckeEis_exists_basis_coeffH1_eq_and_mem_span_and_exists_matrix_of_basis_eq.HeckeEis P2MW.S_HeckeEis_exists_basis_coeffH1_eq_and_mem_span_and_exists_matrix_of_basis_eq.HeckeEis.Lattice"
p2m_reactivate "P2MW.S_HeckeEis_exists_basis_coeffH1_eq_and_mem_span_and_exists_matrix_of_basis_eq.HeckeEis P2MW.S_HeckeEis_exists_basis_coeffH1_eq_and_mem_span_and_exists_matrix_of_basis_eq.HeckeEis.Lattice"

open CongruenceSubgroup HeckeEis.Lattice HeckeEis.Lattice.Transport

theorem solution
    {R : Type} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    {K : Type} [Field K] [Algebra R K] (hRK : Function.Injective (algebraMap R K))
    (N : ℕ) [Group.FG (Gamma0 N)]
    {Λ : Type} [AddCommGroup Λ] [Module R Λ] {V : Type} [AddCommGroup V] [Module K V]
    (ρR : Representation R (Gamma0 N) Λ) (ρ : Representation K (Gamma0 N) V)
    (ι : Λ →+ V) (hιs : ∀ (r : R) (x : Λ), ι (r • x) = algebraMap R K r • ι x)
    (hιρ : ∀ (γ : Gamma0 N) (x : Λ), ι (ρR γ x) = ρ γ (ι x))
    {d : ℕ} (bΛ : Module.Basis (Fin d) R Λ) (bV : Module.Basis (Fin d) K V)
    (hb : ∀ j : Fin d, bV j = ι (bΛ j))
    (Φ : HeckeEis.coeffH1 ρR →+ HeckeEis.coeffH1 ρ)
    (hΦ : ∀ z : ↥(HeckeEis.coeffCocycles ρR), ∃ w : ↥(HeckeEis.coeffCocycles ρ),
      (∀ γ : Gamma0 N, (w : Gamma0 N → V) γ = ι ((z : Gamma0 N → Λ) γ)) ∧
        Φ (HeckeEis.coeffH1Mk ρR z) = HeckeEis.coeffH1Mk ρ w)
    {I : Type} (TR : I → (HeckeEis.coeffH1 ρR →+ HeckeEis.coeffH1 ρR))
    (T : I → (HeckeEis.coeffH1 ρ →+ HeckeEis.coeffH1 ρ))
    (hT : ∀ (l : I) (x : HeckeEis.coeffH1 ρR), Φ (TR l x) = T l (Φ x)) :
    ∃ (t : ℕ) (b : Fin t → HeckeEis.coeffH1 ρR) (c : Module.Basis (Fin t) K (HeckeEis.coeffH1 ρ)),
      (∀ i : Fin t, c i = Φ (b i)) ∧
        (∀ x : HeckeEis.coeffH1 ρR, ∃ r : Fin t → R, Φ x = ∑ i : Fin t, algebraMap R K (r i) • c i) ∧
          ∀ l : I, ∃ A : Matrix (Fin t) (Fin t) R,
            ∀ j : Fin t, T l (c j) = ∑ i : Fin t, algebraMap R K (A i j) • c i := by
  classical

  have hR : IsMatrixOf (matrixRep ρR bΛ) ρR bΛ := isMatrixOf_matrixRep ρR bΛ
  have hK : IsMatrixOf (matrixRep ρR bΛ) ρ bV := isMatrixOf_of_iota hιs hιρ hb
  have hcomp : ∀ x, hK.coordH (Φ x) = Φc (matrixRep ρR bΛ) K (hR.coordH x) :=
    coordH_comp_eq_Φc hιs hb hR hK Φ hΦ

  obtain ⟨t, b, c, hc, hspan⟩ := main hRK (matrixRep ρR bΛ)
  have hcj : ∀ j, c.map hK.coordH.symm j = Φ (hR.coordH.symm (b j)) := by
    intro j
    rw [Module.Basis.map_apply, hc]
    apply hK.coordH.injective
    rw [LinearEquiv.apply_symm_apply, hcomp, LinearEquiv.apply_symm_apply]
  refine ⟨t, fun i => hR.coordH.symm (b i), c.map hK.coordH.symm, hcj, ?_, ?_⟩
  · intro x
    obtain ⟨r, hr⟩ := hspan (hR.coordH x)
    refine ⟨r, ?_⟩
    apply hK.coordH.injective
    rw [hcomp, hr, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, Module.Basis.map_apply, LinearEquiv.apply_symm_apply]
  · intro l
    choose r hr using fun j : Fin t => hspan (hR.coordH (TR l (hR.coordH.symm (b j))))
    refine ⟨Matrix.of fun i j => r j i, fun j => ?_⟩
    rw [hcj, ← hT]
    apply hK.coordH.injective
    rw [hcomp, hr j, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, Module.Basis.map_apply, LinearEquiv.apply_symm_apply, Matrix.of_apply]

end S_HeckeEis_exists_basis_coeffH1_eq_and_mem_span_and_exists_matrix_of_basis_eq
end P2MW
export P2MW.S_HeckeEis_exists_basis_coeffH1_eq_and_mem_span_and_exists_matrix_of_basis_eq (solution)
