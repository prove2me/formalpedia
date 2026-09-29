-- Prove2me | solution 1 for MvFormalGroup.subst_nthSeries_eq_of_map_eq_and_exists_hom_of_ker_pow_eq_bot
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/1af38dfc-c226-544c-a6a4-8fbb1fff9bcd

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MvFormalGroup_subst_nthSeries_eq_of_map_eq_and_exists_hom_of_ker_pow_eq_bot

set_option autoImplicit false

universe u

namespace P2mKcLawRigidity

open MvPowerSeries MvFormalGroup

variable {R : Type u} [CommRing R]

section CoeffsIn

variable {τ : Type*}

def CoeffsIn (J : Ideal R) (s : MvPowerSeries τ R) : Prop := ∀ d, coeff d s ∈ J

theorem CoeffsIn.mono {J J' : Ideal R} (h : J ≤ J') {s : MvPowerSeries τ R} (hs : CoeffsIn J s) :
    CoeffsIn J' s := fun d => h (hs d)

theorem coeffsIn_top (s : MvPowerSeries τ R) : CoeffsIn ⊤ s := fun _ => Submodule.mem_top

theorem coeffsIn_zero (J : Ideal R) : CoeffsIn J (0 : MvPowerSeries τ R) := fun d => by
  rw [map_zero]; exact J.zero_mem

theorem CoeffsIn.add {J : Ideal R} {s t : MvPowerSeries τ R} (hs : CoeffsIn J s) (ht : CoeffsIn J t) :
    CoeffsIn J (s + t) := fun d => by
  rw [map_add]; exact J.add_mem (hs d) (ht d)

theorem CoeffsIn.mul {J J' : Ideal R} {s t : MvPowerSeries τ R} (hs : CoeffsIn J s)
    (ht : CoeffsIn J' t) : CoeffsIn (J * J') (s * t) := by
  classical
  intro d
  rw [coeff_mul]
  exact Ideal.sum_mem _ fun x _ => Ideal.mul_mem_mul (hs x.1) (ht x.2)

theorem CoeffsIn.mul_left {J : Ideal R} (s : MvPowerSeries τ R) {t : MvPowerSeries τ R}
    (ht : CoeffsIn J t) : CoeffsIn J (s * t) := by
  have h := (coeffsIn_top s).mul ht
  rwa [Ideal.top_mul] at h

theorem CoeffsIn.smul {J : Ideal R} (r : R) {t : MvPowerSeries τ R} (ht : CoeffsIn J t) :
    CoeffsIn J (r • t) := fun d => by
  rw [map_smul, smul_eq_mul]; exact J.mul_mem_left r (ht d)

theorem CoeffsIn.pow {J : Ideal R} {s : MvPowerSeries τ R} (hs : CoeffsIn J s) :
    ∀ m : ℕ, CoeffsIn (J ^ m) (s ^ m)
  | 0 => by rw [pow_zero, pow_zero, Ideal.one_eq_top]; exact coeffsIn_top _
  | m + 1 => by rw [pow_succ, pow_succ]; exact (hs.pow m).mul hs

theorem coeffsIn_prod {α : Type*} (J : Ideal R) (s : Finset α) (t : α → MvPowerSeries τ R)
    (k : α → ℕ) (h : ∀ a ∈ s, CoeffsIn (J ^ k a) (t a)) :
    CoeffsIn (J ^ (∑ a ∈ s, k a)) (∏ a ∈ s, t a) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, Finset.prod_empty, pow_zero, Ideal.one_eq_top]
    exact coeffsIn_top _
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha, pow_add]
    exact (h a (Finset.mem_insert_self a s)).mul
      (ih fun b hb => h b (Finset.mem_insert_of_mem hb))

theorem coeffsIn_finsuppProd {σ' : Type*} (J : Ideal R) {c : σ' → MvPowerSeries τ R}
    (hc : ∀ j, CoeffsIn J (c j)) (e : σ' →₀ ℕ) :
    CoeffsIn (J ^ e.degree) (e.prod fun s m => c s ^ m) := by
  rw [Finsupp.prod, Finsupp.degree_apply]
  exact coeffsIn_prod J e.support (fun s => c s ^ e s) (fun s => e s) fun s _ => (hc s).pow (e s)

theorem coeffsIn_ker_iff_map_eq_zero {S : Type*} [CommRing S] (π : R →+* S) (s : MvPowerSeries τ R) :
    CoeffsIn (RingHom.ker π) s ↔ MvPowerSeries.map π s = 0 := by
  constructor
  · intro h
    ext d
    rw [coeff_map, map_zero]
    exact h d
  · intro h d
    have := congrArg (coeff d) h
    rw [coeff_map, map_zero] at this
    exact this

theorem CoeffsIn.eq_zero_of_le_bot {J : Ideal R} (hJ : J ≤ ⊥) {s : MvPowerSeries τ R}
    (hs : CoeffsIn J s) : s = 0 := by
  ext d
  rw [map_zero]
  exact (Submodule.mem_bot R).mp (hJ (hs d))

end CoeffsIn

section Linearise

variable {σ' τ : Type*} [Finite σ']

theorem coeffsIn_sq_subst (J : Ideal R) {c : σ' → MvPowerSeries τ R}
    (hc0 : ∀ j, (c j).constantCoeff = 0) (hc : ∀ j, CoeffsIn J (c j))
    (f : MvPowerSeries σ' R) (hf : ∀ e : σ' →₀ ℕ, e.degree ≤ 1 → coeff e f = 0) :
    CoeffsIn (J ^ 2) (subst c f) := by
  intro d
  rw [coeff_subst (hasSubst_of_constantCoeff_zero hc0)]
  refine finsum_induction (fun x : R => x ∈ J ^ 2) (J ^ 2).zero_mem
    (fun x y hx hy => (J ^ 2).add_mem hx hy) fun e => ?_
  by_cases he : e.degree ≤ 1
  · rw [hf e he, zero_smul]
    exact (J ^ 2).zero_mem
  · rw [smul_eq_mul]
    apply (J ^ 2).mul_mem_left
    have h2 : 2 ≤ e.degree := by omega
    exact (coeffsIn_finsuppProd J hc e).mono (Ideal.pow_le_pow_right h2) d

end Linearise

section NthSeries

variable {h : ℕ} (G : MvFormalGroup h R)

omit [CommRing R] in

theorem exists_eq_single_of_degree_eq_one {σ' : Type*} (e : σ' →₀ ℕ) (he : e.degree = 1) :
    ∃ k, e = Finsupp.single k 1 := by
  classical
  have hne : e ≠ 0 := by
    intro h0
    rw [h0, map_zero] at he
    exact zero_ne_one he
  obtain ⟨k, hk⟩ := Finsupp.support_nonempty_iff.mpr hne
  have hk1 : e k = 1 := by
    have hle : e k ≤ 1 := he ▸ Finsupp.le_degree k e
    have hpos : e k ≠ 0 := Finsupp.mem_support_iff.mp hk
    omega
  refine ⟨k, ?_⟩

  have hsplit : e = Finsupp.single k 1 + (e - Finsupp.single k 1) := by
    ext j
    simp only [Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply, Pi.sub_apply,
      Finsupp.single_apply]
    split_ifs with hkj
    · subst hkj; omega
    · omega
  have hdeg : (e - Finsupp.single k 1).degree = 0 := by
    have := congrArg Finsupp.degree hsplit
    rw [map_add, Finsupp.degree_single, he] at this
    omega
  rw [(Finsupp.degree_eq_zero_iff _).mp hdeg, add_zero] at hsplit
  exact hsplit

theorem coeff_nthSeries_eq_zero_of_degree_le_one (p n : ℕ) (hp : (p : R) ^ n = 0) (i : Fin h)
    (e : Fin h →₀ ℕ) (he : e.degree ≤ 1) : coeff e (G.nthSeries (p ^ n) i) = 0 := by
  rcases Nat.lt_or_ge e.degree 1 with h0 | h1
  · have he0 : e = 0 := (Finsupp.degree_eq_zero_iff e).mp (by omega)
    subst he0
    rw [coeff_zero_eq_constantCoeff_apply]
    exact constantCoeff_nthSeries G (p ^ n) i
  · have he1 : e.degree = 1 := le_antisymm he h1
    obtain ⟨k, rfl⟩ := exists_eq_single_of_degree_eq_one e he1
    have hlin := congrFun (congrFun (linearPart_nthSeries G (p ^ n)) i) k
    change coeff (Finsupp.single k 1) (G.nthSeries (p ^ n) i) = _ at hlin
    rw [hlin, Matrix.smul_apply, Matrix.one_apply, nsmul_eq_mul, Nat.cast_pow, hp, zero_mul]

variable [G.IsComm]

noncomputable def step (p n : ℕ) {τ : Type*} (c : Fin h → MvPowerSeries τ R) : Fin h → MvPowerSeries τ R :=
  fun i => subst c (G.nthSeries (p ^ n) i)

omit [G.IsComm] in
theorem constantCoeff_step (p n : ℕ) {τ : Type*} {c : Fin h → MvPowerSeries τ R}
    (hc0 : ∀ j, (c j).constantCoeff = 0) (i : Fin h) : (step G p n c i).constantCoeff = 0 :=
  constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero hc0) hc0
    (constantCoeff_nthSeries G _ i)

omit [G.IsComm] in

theorem coeffsIn_step (p n : ℕ) (hp : (p : R) ^ n = 0) (I : Ideal R) (j : ℕ) {τ : Type*}
    {c : Fin h → MvPowerSeries τ R} (hc0 : ∀ j, (c j).constantCoeff = 0)
    (hc : ∀ i, CoeffsIn (I ^ (j + 1)) (c i)) (i : Fin h) :
    CoeffsIn (I ^ (j + 2)) (step G p n c i) := by
  have h2 := coeffsIn_sq_subst (I ^ (j + 1)) hc0 hc (G.nthSeries (p ^ n) i)
    (coeff_nthSeries_eq_zero_of_degree_le_one G p n hp i)
  rw [← pow_mul] at h2
  exact h2.mono (Ideal.pow_le_pow_right (by omega))

omit [G.IsComm] in

theorem coeffsIn_iterate_step (p n : ℕ) (hp : (p : R) ^ n = 0) (I : Ideal R) {τ : Type*} (k : ℕ) :
    ∀ {c : Fin h → MvPowerSeries τ R}, (∀ j, (c j).constantCoeff = 0) →
      (∀ i, CoeffsIn (I ^ 1) (c i)) →
      (∀ j, ((step G p n)^[k] c j).constantCoeff = 0) ∧
        ∀ i, CoeffsIn (I ^ (k + 1)) ((step G p n)^[k] c i) := by
  induction k with
  | zero => intro c hc0 hc; exact ⟨hc0, hc⟩
  | succ k ih =>
    intro c hc0 hc
    rw [Function.iterate_succ_apply']
    obtain ⟨h0, h1⟩ := ih hc0 hc
    exact ⟨fun j => constantCoeff_step G p n h0 j, fun i => coeffsIn_step G p n hp I k h0 h1 i⟩

theorem toPowerSeries_natCast_pow (q k : ℕ) :
    Hom.toPowerSeries (((q : End G)) ^ k) = G.nthSeries (q ^ k) := by
  rw [← Nat.cast_pow, End.toPowerSeries_natCast]

theorem subst_pow_eq_iterate (p n : ℕ) {τ : Type*} (k : ℕ) :
    ∀ {c : Fin h → MvPowerSeries τ R}, (∀ j, (c j).constantCoeff = 0) → ∀ i,
      subst c (Hom.toPowerSeries ((((p ^ n : ℕ) : End G)) ^ k) i) = (step G p n)^[k] c i := by
  induction k with
  | zero =>
    intro c hc0 i
    rw [pow_zero, End.toPowerSeries_one, Function.iterate_zero, id_eq]
    exact subst_X (hasSubst_of_constantCoeff_zero hc0) i
  | succ k ih =>
    intro c hc0 i
    rw [pow_succ, End.toPowerSeries_mul, Function.iterate_succ_apply]
    have hq : HasSubst (Hom.toPowerSeries ((p ^ n : ℕ) : End G)) :=
      Hom.hasSubst_toPowerSeries _
    rw [subst_comp_subst_apply hq (hasSubst_of_constantCoeff_zero hc0)]
    have hfam : (fun j => subst c (Hom.toPowerSeries ((p ^ n : ℕ) : End G) j)) = step G p n c := by
      funext j
      rw [End.toPowerSeries_natCast]
      rfl
    rw [hfam]
    exact ih (fun j => constantCoeff_step G p n hc0 j) i

theorem subst_nthSeries_eq_zero_of_coeffsIn (p n μ : ℕ) (hp : (p : R) ^ n = 0) (I : Ideal R)
    (hI : I ^ (μ + 1) = ⊥) {τ : Type*} {c : Fin h → MvPowerSeries τ R}
    (hc0 : ∀ j, (c j).constantCoeff = 0) (hc : ∀ i, CoeffsIn I (c i)) (i : Fin h) :
    subst c (G.nthSeries (p ^ (n * μ)) i) = 0 := by
  have hc' : ∀ i, CoeffsIn (I ^ 1) (c i) := fun i => by rw [pow_one]; exact hc i
  obtain ⟨-, hk⟩ := coeffsIn_iterate_step G p n hp I μ hc0 hc'
  have hE : G.nthSeries (p ^ (n * μ)) = Hom.toPowerSeries ((((p ^ n : ℕ) : End G)) ^ μ) := by
    rw [toPowerSeries_natCast_pow, ← pow_mul]
  rw [hE, subst_pow_eq_iterate G p n μ hc0 i]
  exact (hk i).eq_zero_of_le_bot hI.le

end NthSeries

section GroupStep

variable {g h : ℕ}

theorem hom_subst_elim (F : MvFormalGroup g R) (G : MvFormalGroup h R) (φ : F.Hom G) {τ : Type*}
    {a b : Fin g → MvPowerSeries τ R} (ha : ∀ j, (a j).constantCoeff = 0)
    (hb : ∀ j, (b j).constantCoeff = 0) (i : Fin h) :
    subst (fun j => subst (Sum.elim a b) (F.toPowerSeries j)) (φ.toPowerSeries i) =
      subst (Sum.elim (fun j => subst a (φ.toPowerSeries j)) fun j => subst b (φ.toPowerSeries j))
        (G.toPowerSeries i) := by
  have hab : HasSubst (Sum.elim a b) := hasSubst_elim ha hb
  have hsa : HasSubst a := hasSubst_of_constantCoeff_zero ha
  have hsb : HasSubst b := hasSubst_of_constantCoeff_zero hb
  have hXl : HasSubst (fun l : Fin g => (X (Sum.inl l) : MvPowerSeries (Fin g ⊕ Fin g) R)) :=
    hasSubst_of_constantCoeff_zero fun l => constantCoeff_X _
  have hXr : HasSubst (fun l : Fin g => (X (Sum.inr l) : MvPowerSeries (Fin g ⊕ Fin g) R)) :=
    hasSubst_of_constantCoeff_zero fun l => constantCoeff_X _
  have hA : HasSubst (Sum.elim
      (fun j => subst (fun l => (X (Sum.inl l) : MvPowerSeries (Fin g ⊕ Fin g) R))
        (φ.toPowerSeries j))
      fun j => subst (fun l => (X (Sum.inr l) : MvPowerSeries (Fin g ⊕ Fin g) R))
        (φ.toPowerSeries j)) := by
    apply hasSubst_of_constantCoeff_zero
    rintro (j | j) <;>
      exact constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero fun l => constantCoeff_X _)
        (fun l => constantCoeff_X _) (φ.constantCoeff_eq_zero j)
  have key := congrArg (subst (Sum.elim a b)) (φ.subst_eq i)
  rw [subst_comp_subst_apply F.hasSubst_toPowerSeries hab, subst_comp_subst_apply hA hab] at key
  have hfam : (fun s => subst (Sum.elim a b) ((Sum.elim
      (fun j => subst (fun l => (X (Sum.inl l) : MvPowerSeries (Fin g ⊕ Fin g) R))
        (φ.toPowerSeries j))
      fun j => subst (fun l => (X (Sum.inr l) : MvPowerSeries (Fin g ⊕ Fin g) R))
        (φ.toPowerSeries j)) s))
      = Sum.elim (fun j => subst a (φ.toPowerSeries j)) fun j => subst b (φ.toPowerSeries j) := by
    funext s
    rcases s with j | j
    · show subst (Sum.elim a b) (subst (fun l => (X (Sum.inl l) : MvPowerSeries (Fin g ⊕ Fin g) R))
          (φ.toPowerSeries j)) = subst a (φ.toPowerSeries j)
      rw [subst_comp_subst_apply hXl hab]
      congr 1
      funext l
      exact subst_X hab (Sum.inl l)
    · show subst (Sum.elim a b) (subst (fun l => (X (Sum.inr l) : MvPowerSeries (Fin g ⊕ Fin g) R))
          (φ.toPowerSeries j)) = subst b (φ.toPowerSeries j)
      rw [subst_comp_subst_apply hXr hab]
      congr 1
      funext l
      exact subst_X hab (Sum.inr l)
  rw [hfam] at key
  exact key

variable (G : MvFormalGroup h R) [G.IsComm]

omit [G.IsComm] in

theorem map_negSeries {S : Type*} [CommRing S] (π : R →+* S) {τ : Type*}
    {b : Fin h → MvPowerSeries τ R} (hb : ∀ j, (b j).constantCoeff = 0) :
    (fun j => MvPowerSeries.map π (negSeries G b j)) =
      negSeries (G.map π) fun j => MvPowerSeries.map π (b j) := by
  have hnb : ∀ j, (negSeries G b j).constantCoeff = 0 := constantCoeff_negSeries G b
  refine negSeries_unique (G.map π) (fun j => by rw [constantCoeff_map, hb j, map_zero])
    (fun j => by rw [constantCoeff_map, hnb j, map_zero]) fun i => ?_
  have key := congrArg (MvPowerSeries.map π) (subst_elim_negSeries G hb i)
  rw [map_subst (hasSubst_elim hb hnb), map_zero] at key
  have hfam : (fun s => MvPowerSeries.map π (Sum.elim b (negSeries G b) s)) =
      Sum.elim (fun j => MvPowerSeries.map π (b j)) fun j => MvPowerSeries.map π (negSeries G b j) := by
    funext s; rcases s with j | j <;> rfl
  rw [hfam] at key
  exact key

theorem subst_nthSeries_eq_of_map_eq {S : Type*} [CommRing S] (π : R →+* S) (μ : ℕ)
    (hI : RingHom.ker π ^ (μ + 1) = ⊥) (p n : ℕ) (hp : (p : R) ^ n = 0) {τ : Type*}
    {a b : Fin h → MvPowerSeries τ R} (ha : ∀ j, (a j).constantCoeff = 0)
    (hb : ∀ j, (b j).constantCoeff = 0)
    (hab : ∀ i, MvPowerSeries.map π (a i) = MvPowerSeries.map π (b i)) (i : Fin h) :
    subst a (G.nthSeries (p ^ (n * μ)) i) = subst b (G.nthSeries (p ^ (n * μ)) i) := by

  set nb := negSeries G b with hnb_def
  have hnb : ∀ j, (nb j).constantCoeff = 0 := constantCoeff_negSeries G b
  let c : Fin h → MvPowerSeries τ R := fun j => subst (Sum.elim a nb) (G.toPowerSeries j)
  have hc0 : ∀ j, (c j).constantCoeff = 0 := fun j => constantCoeff_subst_elim G ha hnb j

  have hc : ∀ j, CoeffsIn (RingHom.ker π) (c j) := by
    intro j
    rw [coeffsIn_ker_iff_map_eq_zero]
    show MvPowerSeries.map π (subst (Sum.elim a nb) (G.toPowerSeries j)) = 0
    rw [map_subst (hasSubst_elim ha hnb)]
    have hfam : (fun s => MvPowerSeries.map π (Sum.elim a nb s)) =
        Sum.elim (fun j => MvPowerSeries.map π (b j))
          (negSeries (G.map π) fun j => MvPowerSeries.map π (b j)) := by
      rw [← map_negSeries G π hb]
      funext s
      rcases s with j | j
      · exact hab j
      · rfl
    rw [hfam]
    exact subst_elim_negSeries (G.map π) (fun j => by rw [constantCoeff_map, hb j, map_zero]) j

  have hacb : a = fun j => subst (Sum.elim c b) (G.toPowerSeries j) := by
    funext j
    show a j = subst (Sum.elim (fun j' => subst (Sum.elim a nb) (G.toPowerSeries j')) b)
      (G.toPowerSeries j)
    rw [subst_elim_assoc G ha hnb hb j]
    have hin : (fun j' => subst (Sum.elim nb b) (G.toPowerSeries j')) = fun _ => 0 := by
      funext j'
      exact subst_elim_negSeries_left G hb j'
    rw [hin, subst_elim_zero_right G ha j]

  set E : End G := ((p ^ (n * μ) : ℕ) : End G) with hE_def
  have hE : G.nthSeries (p ^ (n * μ)) = Hom.toPowerSeries E := by
    rw [hE_def, End.toPowerSeries_natCast]
  rw [hE, hacb, hom_subst_elim G G E hc0 hb i]
  have hEc : (fun j => subst c (Hom.toPowerSeries E j)) = fun _ => 0 := by
    funext j
    rw [← hE]
    exact subst_nthSeries_eq_zero_of_coeffsIn G p n μ hp (RingHom.ker π) hI hc0 hc j
  rw [hEc]
  exact subst_elim_zero_left G
    (fun j => constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero hb) hb
      (E.constantCoeff_eq_zero j)) i

end GroupStep

section LiftHom

variable {g h : ℕ} (F : MvFormalGroup g R) (G : MvFormalGroup h R) [G.IsComm]

theorem exists_hom {S : Type*} [CommRing S] (π : R →+* S) (μ : ℕ)
    (hI : RingHom.ker π ^ (μ + 1) = ⊥) (p n : ℕ) (hp : (p : R) ^ n = 0)
    (φ : Fin h → MvPowerSeries (Fin g) R) (hφ : ∀ i, (φ i).constantCoeff = 0)
    (f₀ : (F.map π).Hom (G.map π)) (hf₀ : ∀ i, f₀.toPowerSeries i = MvPowerSeries.map π (φ i)) :
    ∃ f : F.Hom G, ∀ i, f.toPowerSeries i = subst φ (G.nthSeries (p ^ (n * μ)) i) := by

  let Xl : Fin g → MvPowerSeries (Fin g ⊕ Fin g) R := fun l => X (Sum.inl l)
  let Xr : Fin g → MvPowerSeries (Fin g ⊕ Fin g) R := fun l => X (Sum.inr l)
  have hXl0 : ∀ l, (Xl l).constantCoeff = 0 := fun l => constantCoeff_X _
  have hXr0 : ∀ l, (Xr l).constantCoeff = 0 := fun l => constantCoeff_X _
  have hXl : HasSubst Xl := hasSubst_of_constantCoeff_zero hXl0
  have hXr : HasSubst Xr := hasSubst_of_constantCoeff_zero hXr0
  have hφs : HasSubst φ := hasSubst_of_constantCoeff_zero hφ
  let φl : Fin h → MvPowerSeries (Fin g ⊕ Fin g) R := fun j => subst Xl (φ j)
  let φr : Fin h → MvPowerSeries (Fin g ⊕ Fin g) R := fun j => subst Xr (φ j)
  have hφl : ∀ j, (φl j).constantCoeff = 0 := fun j => constantCoeff_subst_eq_zero hXl hXl0 (hφ j)
  have hφr : ∀ j, (φr j).constantCoeff = 0 := fun j => constantCoeff_subst_eq_zero hXr hXr0 (hφ j)
  let A : Fin h → MvPowerSeries (Fin g ⊕ Fin g) R := fun j => subst F.toPowerSeries (φ j)
  let B : Fin h → MvPowerSeries (Fin g ⊕ Fin g) R := fun j => subst (Sum.elim φl φr) (G.toPowerSeries j)
  have hA0 : ∀ j, (A j).constantCoeff = 0 := fun j =>
    constantCoeff_subst_eq_zero F.hasSubst_toPowerSeries F.constantCoeff_eq_zero (hφ j)
  have hB0 : ∀ j, (B j).constantCoeff = 0 := fun j => constantCoeff_subst_elim G hφl hφr j

  have hAB : ∀ j, MvPowerSeries.map π (A j) = MvPowerSeries.map π (B j) := by
    intro j
    show MvPowerSeries.map π (subst F.toPowerSeries (φ j)) =
      MvPowerSeries.map π (subst (Sum.elim φl φr) (G.toPowerSeries j))
    rw [map_subst F.hasSubst_toPowerSeries, map_subst (hasSubst_elim hφl hφr), ← hf₀ j]
    have h1 : (fun s => MvPowerSeries.map π (F.toPowerSeries s)) = (F.map π).toPowerSeries := rfl
    have h2 : (fun s => MvPowerSeries.map π (Sum.elim φl φr s)) =
        Sum.elim (fun j => subst (fun l => (X (Sum.inl l) : MvPowerSeries (Fin g ⊕ Fin g) S))
            (f₀.toPowerSeries j))
          fun j => subst (fun l => (X (Sum.inr l) : MvPowerSeries (Fin g ⊕ Fin g) S))
            (f₀.toPowerSeries j) := by
      funext s
      rcases s with j | j
      · show MvPowerSeries.map π (subst Xl (φ j)) =
          subst (fun l => (X (Sum.inl l) : MvPowerSeries (Fin g ⊕ Fin g) S)) (f₀.toPowerSeries j)
        rw [map_subst hXl, hf₀ j]
        congr 1
        funext l
        exact map_X π (Sum.inl l)
      · show MvPowerSeries.map π (subst Xr (φ j)) =
          subst (fun l => (X (Sum.inr l) : MvPowerSeries (Fin g ⊕ Fin g) S)) (f₀.toPowerSeries j)
        rw [map_subst hXr, hf₀ j]
        congr 1
        funext l
        exact map_X π (Sum.inr l)
    rw [h1, h2]
    exact f₀.subst_eq j
  have hN := fun i => subst_nthSeries_eq_of_map_eq G π μ hI p n hp hA0 hB0 hAB i

  set E : End G := ((p ^ (n * μ) : ℕ) : End G) with hE_def
  have hE : G.nthSeries (p ^ (n * μ)) = Hom.toPowerSeries E := by
    rw [hE_def, End.toPowerSeries_natCast]
  refine ⟨⟨fun i => subst φ (G.nthSeries (p ^ (n * μ)) i), fun i =>
    constantCoeff_subst_eq_zero hφs hφ (constantCoeff_nthSeries G _ i), fun i => ?_⟩, fun i => rfl⟩

  rw [subst_comp_subst_apply hφs F.hasSubst_toPowerSeries]
  change subst A (G.nthSeries (p ^ (n * μ)) i) = _
  rw [hN i, hE]
  change subst (fun j => subst (Sum.elim φl φr) (G.toPowerSeries j)) (Hom.toPowerSeries E i) = _
  rw [hom_subst_elim G G E hφl hφr i]
  congr 1
  funext s
  rcases s with j | j
  · show subst φl (Hom.toPowerSeries E j) = subst Xl (subst φ (Hom.toPowerSeries E j))
    rw [subst_comp_subst_apply hφs hXl]
  · show subst φr (Hom.toPowerSeries E j) = subst Xr (subst φ (Hom.toPowerSeries E j))
    rw [subst_comp_subst_apply hφs hXr]

end LiftHom

end P2mKcLawRigidity

open P2mKcLawRigidity in
theorem solution
    {R S : Type u} [CommRing R] [CommRing S] (π : R →+* S) (μ : ℕ)
    (hI : RingHom.ker π ^ (μ + 1) = ⊥) (p n : ℕ) (hp : (p : R) ^ n = 0)
    {h : ℕ} (G : MvFormalGroup h R) [G.IsComm] :
    (∀ (τ : Type) (a b : Fin h → MvPowerSeries τ R),
        (∀ i, (a i).constantCoeff = 0) → (∀ i, (b i).constantCoeff = 0) →
        (∀ i, MvPowerSeries.map π (a i) = MvPowerSeries.map π (b i)) →
        ∀ i, MvPowerSeries.subst a (G.nthSeries (p ^ (n * μ)) i) =
          MvPowerSeries.subst b (G.nthSeries (p ^ (n * μ)) i)) ∧
    (∀ (g : ℕ) (F : MvFormalGroup g R) (φ : Fin h → MvPowerSeries (Fin g) R),
        (∀ i, (φ i).constantCoeff = 0) →
        (∃ f₀ : (F.map π).Hom (G.map π), ∀ i, f₀.toPowerSeries i = MvPowerSeries.map π (φ i)) →
        ∃ f : F.Hom G, ∀ i, f.toPowerSeries i = MvPowerSeries.subst φ (G.nthSeries (p ^ (n * μ)) i)) :=
  ⟨fun _ _ _ ha hb hab i => subst_nthSeries_eq_of_map_eq G π μ hI p n hp ha hb hab i,
    fun _ F φ hφ ⟨f₀, hf₀⟩ => exists_hom F G π μ hI p n hp φ hφ f₀ hf₀⟩

end S_MvFormalGroup_subst_nthSeries_eq_of_map_eq_and_exists_hom_of_ker_pow_eq_bot
end P2MW
export P2MW.S_MvFormalGroup_subst_nthSeries_eq_of_map_eq_and_exists_hom_of_ker_pow_eq_bot (solution)
